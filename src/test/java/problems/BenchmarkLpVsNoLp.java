package problems;

import java.io.IOException;
import java.io.InputStream;
import java.lang.management.ManagementFactory;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Benchmark runner comparing ACE with LP enabled and disabled on the same
 * optimization instances.
 *
 * The benchmark is proof-oriented: it highlights whether optimality is proved
 * within the same budget, the final objective gap, and the explored nodes.
 *
 * Usage examples:
 * ./gradlew benchmarkLpVsNoLp
 * ./gradlew benchmarkLpVsNoLp -PbenchmarkArgs="--iterations=1 --warmup=0 --arg=-t=30s --copdataset --limit=10"
 * ./gradlew benchmarkLpVsNoLp -PbenchmarkArgs="--arg=-t=20s ~/Codes/research/pycsp3-solvers-extra/examples/XCSP25/COP25/"
 * ./gradlew benchmarkLpVsNoLp -PbenchmarkArgs="--filter=Warehouse --arg=-lbtn=63 /cop/Warehouse-Warehouse_example"
 */
public final class BenchmarkLpVsNoLp {

	private static final List<String> DEFAULT_INSTANCES = List.of(
			"/cop/ChangeMaking-10",
			"/cop/Cutstock-Cutstock_small",
			"/cop/Knapsack-Knapsack_20-50-00",
			"/cop/GraphMaxAcyclic-cnt-GraphMaxAcyclic_example",
			"/cop/PizzaVoucher-PizzaVoucher_pizza6",
			"/cop/Warehouse-Warehouse_example");

	private static final List<String> COP_DATASET_DIR_CANDIDATES = List.of(
			"./XCSP25/COP25",
			"./data/XCSP25/COP25",
			"./benchmarks/XCSP25/COP25",
			"./examples/XCSP25/COP25");

	private static final Map<String, Path> EXTRACTED_RESOURCES = new LinkedHashMap<>();

	private enum Mode {
		LP_ON(true, "LP"),
		LP_OFF(false, "NoLP");

		final boolean enabled;
		final String label;

		Mode(boolean enabled, String label) {
			this.enabled = enabled;
			this.label = label;
		}
	}

	private static final class Options {
		int iterations = 3;
		int warmup = 1;
		int limit = Integer.MAX_VALUE;
		String filter;
		String csvPath = "build/reports/benchmark-lp-vs-nolp.csv";
		boolean includeCopDataset;
		final List<String> directorySpecs = new ArrayList<>();
		final List<String> solverArgs = new ArrayList<>();
		final List<String> instances = new ArrayList<>();
	}

	private static final class RunMetrics {
		final Mode mode;
		final boolean failed;
		final double wallSeconds;
		final double searchSeconds;
		final long bestBound;
		final long minBound;
		final long maxBound;
		final long nodes;
		final long wrongDecisions;
		final long foundSolutions;
		final boolean provedOptimum;
		final Long finiteGap;
		final String stopping;

		RunMetrics(Mode mode, Map<String, String> values) {
			this.mode = mode;
			this.failed = parseBoolean(values, "failed", false);
			this.wallSeconds = parseDouble(values, "wallSeconds", 0.0);
			this.searchSeconds = parseDouble(values, "searchSeconds", 0.0);
			this.bestBound = parseLong(values, "bestBound", 0L);
			this.nodes = parseLong(values, "nodes", 0L);
			this.wrongDecisions = parseLong(values, "wrongDecisions", 0L);
			this.foundSolutions = parseLong(values, "foundSolutions", 0L);
			this.stopping = values.getOrDefault("stopping", "ERROR");
			this.minBound = parseLong(values, "minBound", Long.MIN_VALUE);
			this.maxBound = parseLong(values, "maxBound", Long.MAX_VALUE);
			this.provedOptimum = parseBoolean(values, "provedOptimum", false);
			this.finiteGap = minBound != Long.MIN_VALUE && maxBound != Long.MAX_VALUE ? Math.max(0L, maxBound - minBound) : null;
		}
	}

	private static final class Aggregate {
		final Mode mode;
		int runs;
		int failedRuns;
		int runsWithSolution;
		int runsProvedOptimum;
		int finiteGapRuns;
		double wallSeconds;
		double searchSeconds;
		double nodes;
		double wrongDecisions;
		double finiteGapSum;
		long firstBestBound;
		long firstMinBound;
		long firstMaxBound;
		boolean bestBoundConsistent = true;
		boolean boundsConsistent = true;
		String firstStopping = "";
		boolean stoppingConsistent = true;

		Aggregate(Mode mode) {
			this.mode = mode;
		}

		void add(RunMetrics metrics) {
			if (runs == 0) {
				firstBestBound = metrics.bestBound;
				firstMinBound = metrics.minBound;
				firstMaxBound = metrics.maxBound;
				firstStopping = metrics.stopping;
			} else {
				bestBoundConsistent &= firstBestBound == metrics.bestBound;
				boundsConsistent &= firstMinBound == metrics.minBound && firstMaxBound == metrics.maxBound;
				stoppingConsistent &= firstStopping.equals(metrics.stopping);
			}
			runs++;
			if (metrics.failed)
				failedRuns++;
			if (metrics.foundSolutions > 0)
				runsWithSolution++;
			if (metrics.provedOptimum)
				runsProvedOptimum++;
			if (metrics.finiteGap != null) {
				finiteGapRuns++;
				finiteGapSum += metrics.finiteGap;
			}
			wallSeconds += metrics.wallSeconds;
			searchSeconds += metrics.searchSeconds;
			nodes += metrics.nodes;
			wrongDecisions += metrics.wrongDecisions;
		}

		double avgWallSeconds() {
			return wallSeconds / runs;
		}

		double avgSearchSeconds() {
			return searchSeconds / runs;
		}

		double avgNodes() {
			return nodes / runs;
		}

		double avgWrongDecisions() {
			return wrongDecisions / runs;
		}

		double avgFiniteGap() {
			return finiteGapRuns == 0 ? Double.POSITIVE_INFINITY : finiteGapSum / finiteGapRuns;
		}

		boolean alwaysProvedOptimum() {
			return runs > 0 && runsProvedOptimum == runs;
		}

		boolean hasFailures() {
			return failedRuns > 0;
		}

		String proofLabel() {
			if (runsProvedOptimum == runs)
				return "yes";
			if (runsProvedOptimum == 0)
				return "no";
			return runsProvedOptimum + "/" + runs;
		}

		String solutionLabel() {
			if (runsWithSolution == runs)
				return "yes";
			if (runsWithSolution == 0)
				return "no";
			return runsWithSolution + "/" + runs;
		}

		String boundsLabel() {
			if (alwaysProvedOptimum()) {
				if (runsWithSolution == 0)
					return "proved";
				return bestBoundConsistent ? formatLong(firstBestBound) + ".." + formatLong(firstBestBound) : "proved";
			}
			if (!boundsConsistent)
				return "varies";
			return formatLong(firstMinBound) + ".." + formatLong(firstMaxBound);
		}

		String gapLabel() {
			if (alwaysProvedOptimum())
				return "0";
			if (finiteGapRuns == 0)
				return "inf";
			return finiteGapRuns == runs ? formatCount(avgFiniteGap()) : "~" + formatCount(avgFiniteGap());
		}

		String bestLabel() {
			if (runsWithSolution == 0)
				return "-";
			return bestBoundConsistent ? formatLong(firstBestBound) : "varies";
		}

		String stoppingLabel() {
			return stoppingConsistent ? firstStopping : "varies";
		}
	}

	private static final class BenchmarkResult {
		final String spec;
		final String displayName;
		final Aggregate withLp = new Aggregate(Mode.LP_ON);
		final Aggregate withoutLp = new Aggregate(Mode.LP_OFF);

		BenchmarkResult(String spec, String displayName) {
			this.spec = spec;
			this.displayName = displayName;
		}
	}

	public static void main(String[] args) {
		Options options = parseOptions(args);
		List<String> instances = collectInstances(options);
		System.out.println("Benchmark LP vs NoLP");
		System.out.println("focus=proof-of-optimality gap nodes");
		System.out.println("iterations=" + options.iterations + " warmup=" + options.warmup + " commonArgs="
				+ (options.solverArgs.isEmpty() ? "[]" : options.solverArgs));
		System.out.println("instances=" + instances.size());
		if (options.includeCopDataset)
			System.out.println("copdataset=" + resolveCopDatasetDir());
		if (options.filter != null)
			System.out.println("filter=" + options.filter);
		if (!options.directorySpecs.isEmpty())
			System.out.println("directories=" + options.directorySpecs.stream().map(BenchmarkLpVsNoLp::expandHome).collect(Collectors.toList()));
		System.out.println();
		if (instances.isEmpty()) {
			System.out.println("No instance matched the current selection.");
			return;
		}

		List<BenchmarkResult> results = new ArrayList<>();
		for (String spec : instances) {
			String resolved = resolveSpec(spec);
			BenchmarkResult result = new BenchmarkResult(spec, displayName(spec, resolved));
			runWarmups(resolved, options);
			runMeasurements(resolved, options, result);
			results.add(result);
			printInstanceSummary(result);
		}
		printGlobalSummary(results);
		writeCsv(results, options);
	}

	private static Options parseOptions(String[] args) {
		Options options = new Options();
		for (String arg : args) {
			if (arg.startsWith("--iterations=")) {
				options.iterations = Integer.parseInt(arg.substring("--iterations=".length()));
			} else if (arg.startsWith("--warmup=")) {
				options.warmup = Integer.parseInt(arg.substring("--warmup=".length()));
			} else if (arg.startsWith("--limit=")) {
				options.limit = Integer.parseInt(arg.substring("--limit=".length()));
			} else if (arg.startsWith("--filter=")) {
				options.filter = arg.substring("--filter=".length());
			} else if (arg.startsWith("--csv=")) {
				options.csvPath = arg.substring("--csv=".length());
			} else if (arg.equals("--copdataset") || arg.equals("--cop-dataset") || arg.equals("--cop25")) {
				options.includeCopDataset = true;
			} else if (arg.startsWith("--dir=")) {
				options.directorySpecs.add(arg.substring("--dir=".length()));
			} else if (arg.startsWith("--arg=")) {
				options.solverArgs.add(arg.substring("--arg=".length()));
			} else {
				options.instances.add(arg);
			}
		}
		return options;
	}

	private static List<String> collectInstances(Options options) {
		List<String> rawSpecs = new ArrayList<>();
		if (options.instances.isEmpty() && options.directorySpecs.isEmpty())
			rawSpecs.addAll(DEFAULT_INSTANCES);
		rawSpecs.addAll(options.instances);
		rawSpecs.addAll(options.directorySpecs);
		if (options.includeCopDataset)
			rawSpecs.add(resolveCopDatasetDir());

		LinkedHashSet<String> collected = new LinkedHashSet<>();
		for (String spec : rawSpecs) {
			for (String expanded : expandSpec(spec)) {
				if (matchesFilter(expanded, options.filter))
					collected.add(expanded);
			}
		}
		List<String> instances = new ArrayList<>(collected);
		if (instances.size() > options.limit)
			return new ArrayList<>(instances.subList(0, options.limit));
		return instances;
	}

	private static boolean matchesFilter(String spec, String filter) {
		if (filter == null || filter.isEmpty())
			return true;
		String normalizedFilter = filter.toLowerCase(Locale.ROOT);
		String normalizedSpec = spec.toLowerCase(Locale.ROOT);
		return normalizedSpec.contains(normalizedFilter);
	}

	private static List<String> expandSpec(String spec) {
		String expanded = expandHome(spec);
		Path path = Paths.get(expanded);
		if (Files.isDirectory(path))
			return scanDirectory(path);
		if (Files.exists(path))
			return List.of(path.toString());
		return List.of(spec);
	}

	private static List<String> scanDirectory(Path directory) {
		try (Stream<Path> stream = Files.list(directory)) {
			return stream.filter(Files::isRegularFile)
					.filter(path -> {
						String name = path.getFileName().toString();
						return name.endsWith(".xml.lzma") || name.endsWith(".xml");
					})
					.sorted()
					.map(Path::toString)
					.collect(Collectors.toList());
		} catch (IOException e) {
			throw new RuntimeException("Cannot list benchmark directory: " + directory, e);
		}
	}

	private static void runWarmups(String resolved, Options options) {
		for (int i = 0; i < options.warmup; i++) {
			Mode[] order = orderedModes(i);
			for (Mode mode : order)
				runOne(resolved, options.solverArgs, mode);
		}
	}

	private static void runMeasurements(String resolved, Options options, BenchmarkResult result) {
		for (int i = 0; i < options.iterations; i++) {
			Mode[] order = orderedModes(i);
			for (Mode mode : order) {
				RunMetrics metrics = runOne(resolved, options.solverArgs, mode);
				(mode == Mode.LP_ON ? result.withLp : result.withoutLp).add(metrics);
			}
		}
	}

	private static Mode[] orderedModes(int iteration) {
		return iteration % 2 == 0 ? new Mode[] { Mode.LP_ON, Mode.LP_OFF } : new Mode[] { Mode.LP_OFF, Mode.LP_ON };
	}

	private static RunMetrics runOne(String resolved, List<String> commonArgs, Mode mode) {
		List<String> tokens = buildArgs(resolved, commonArgs, mode);
		return new RunMetrics(mode, runWorker(tokens));
	}

	private static List<String> buildArgs(String resolved, List<String> commonArgs, Mode mode) {
		List<String> tokens = new ArrayList<>();
		tokens.add(resolved);
		tokens.add("-v=-1");
		tokens.add("-lp=" + mode.enabled);
		tokens.addAll(commonArgs);
		return tokens;
	}

	private static String resolveSpec(String spec) {
		String expanded = expandHome(spec);
		Path path = Paths.get(expanded);
		if (Files.exists(path))
			return path.toString();
		if (expanded.endsWith(".xml.lzma"))
			return expanded;
		String resourceName = expanded.endsWith(".xml") || expanded.endsWith(".lzma") ? expanded : expanded + ".xml.lzma";
		URL resource = BenchmarkLpVsNoLp.class.getResource(resourceName);
		return resource != null ? materializeResource(resourceName, resource) : expanded;
	}

	private static String materializeResource(String resourceName, URL resource) {
		if ("file".equalsIgnoreCase(resource.getProtocol()))
			return Paths.get(resource.getPath()).toString();
		Path cached = EXTRACTED_RESOURCES.get(resourceName);
		if (cached != null && Files.exists(cached))
			return cached.toString();
		String fileName = Paths.get(resourceName).getFileName().toString();
		String prefix = fileName.contains(".") ? fileName.substring(0, fileName.indexOf('.')) : fileName;
		if (prefix.length() < 3)
			prefix = "ace" + prefix;
		String suffix = fileName.contains(".") ? fileName.substring(fileName.indexOf('.')) : ".tmp";
		try {
			Path extracted = Files.createTempFile("ace-benchmark-" + prefix + "-", suffix);
			try (InputStream in = resource.openStream()) {
				Files.copy(in, extracted, StandardCopyOption.REPLACE_EXISTING);
			}
			extracted.toFile().deleteOnExit();
			EXTRACTED_RESOURCES.put(resourceName, extracted);
			return extracted.toString();
		} catch (IOException e) {
			throw new RuntimeException("Cannot extract benchmark resource: " + resourceName, e);
		}
	}

	private static String displayName(String spec, String resolved) {
		String candidate = spec;
		if (candidate.endsWith(".xml.lzma"))
			candidate = candidate.substring(0, candidate.length() - ".xml.lzma".length());
		else if (candidate.endsWith(".xml"))
			candidate = candidate.substring(0, candidate.length() - ".xml".length());
		int slash = Math.max(candidate.lastIndexOf('/'), candidate.lastIndexOf('\\'));
		if (slash >= 0 && slash + 1 < candidate.length())
			candidate = candidate.substring(slash + 1);
		if (!candidate.isEmpty())
			return candidate;
		return resolved;
	}

	private static void printInstanceSummary(BenchmarkResult result) {
		Aggregate lp = result.withLp;
		Aggregate noLp = result.withoutLp;
		String[] headers = { "mode", "proof", "sol", "best", "bounds", "gap", "nodes", "wall", "search", "stop" };
		int[] widths = { 6, 7, 5, 10, 17, 10, 12, 8, 8, 6 };
		boolean[] rightAligned = { false, false, false, true, false, true, true, true, true, false };
		System.out.println(result.displayName);
		System.out.println(fixedRow(headers, widths, rightAligned));
		System.out.println(rule(widths));
		System.out.println(row(lp, widths, rightAligned));
		System.out.println(row(noLp, widths, rightAligned));
		System.out.println(comparisonLine(lp, noLp));
		System.out.println();
	}

	private static String row(Aggregate aggregate, int[] widths, boolean[] rightAligned) {
		String[] values = { aggregate.mode.label, aggregate.proofLabel(), aggregate.solutionLabel(), aggregate.bestLabel(), aggregate.boundsLabel(),
				aggregate.gapLabel(), formatCount(aggregate.avgNodes()), formatTime(aggregate.avgWallSeconds()),
				formatTime(aggregate.avgSearchSeconds()), compactStopping(aggregate.stoppingLabel()) };
		return fixedRow(values, widths, rightAligned);
	}

	private static String comparisonLine(Aggregate lp, Aggregate noLp) {
		if (lp.hasFailures() || noLp.hasFailures())
			return "comparison: n/a (error)";
		String proof = lp.alwaysProvedOptimum() == noLp.alwaysProvedOptimum() ? (lp.alwaysProvedOptimum() ? "proof: both" : "proof: neither")
				: lp.alwaysProvedOptimum() ? "proof: LP only" : "proof: NoLP only";
		String gap = compareMetric("gap", lp.avgFiniteGap(), noLp.avgFiniteGap(), true);
		String nodes = compareMetric("nodes", lp.avgNodes(), noLp.avgNodes(), true);
		return proof + "  " + gap + "  " + nodes;
	}

	private static void printGlobalSummary(List<BenchmarkResult> results) {
		int lpProved = 0;
		int noLpProved = 0;
		int lpOnlyProofs = 0;
		int noLpOnlyProofs = 0;
		int lpBetterGap = 0;
		int noLpBetterGap = 0;
		int equalGap = 0;
		int lpFewerNodes = 0;
		int noLpFewerNodes = 0;
		int equalNodes = 0;
		int instanceWidth = Math.max("instance".length(),
				results.stream().map(result -> result.displayName.length()).max(Integer::compareTo).orElse(0));
		String[] headers = { padRight("instance", instanceWidth), "LP", "NoLP", "LP gap", "NoLP gap", "LP nodes", "NoLP nodes" };
		int[] widths = { instanceWidth, 4, 4, 10, 10, 12, 12 };
		boolean[] rightAligned = { false, false, false, true, true, true, true };

		System.out.println("Summary");
		System.out.println(fixedRow(headers, widths, rightAligned));
		System.out.println(rule(widths));
		for (BenchmarkResult result : results) {
			Aggregate lp = result.withLp;
			Aggregate noLp = result.withoutLp;
			boolean lpOpt = lp.alwaysProvedOptimum();
			boolean noLpOpt = noLp.alwaysProvedOptimum();
			if (lpOpt)
				lpProved++;
			if (noLpOpt)
				noLpProved++;
			if (lpOpt && !noLpOpt)
				lpOnlyProofs++;
			if (!lpOpt && noLpOpt)
				noLpOnlyProofs++;

			double lpGap = lp.avgFiniteGap();
			double noLpGap = noLp.avgFiniteGap();
			double lpNodes = lp.avgNodes();
			double noLpNodes = noLp.avgNodes();
			if (!lp.hasFailures() && !noLp.hasFailures()) {
				if (lpGap < noLpGap)
					lpBetterGap++;
				else if (lpGap > noLpGap)
					noLpBetterGap++;
				else
					equalGap++;

				if (lpNodes < noLpNodes)
					lpFewerNodes++;
				else if (lpNodes > noLpNodes)
					noLpFewerNodes++;
				else
					equalNodes++;
			}

			String[] values = { result.displayName, lp.proofLabel(), noLp.proofLabel(), lp.gapLabel(), noLp.gapLabel(), formatCount(lpNodes),
					formatCount(noLpNodes) };
			System.out.println(fixedRow(values, widths, rightAligned));
		}

		System.out.println();
		System.out.println("LP proves optimum on " + lpProved + "/" + results.size() + " instance(s); NoLP on " + noLpProved + "/" + results.size()
				+ ".");
		System.out.println("LP-only proofs: " + lpOnlyProofs + "  NoLP-only proofs: " + noLpOnlyProofs + ".");
		System.out.println(
				"Smaller final gap: LP " + lpBetterGap + "  NoLP " + noLpBetterGap + "  tie " + equalGap + ".");
		System.out.println("Fewer explored nodes: LP " + lpFewerNodes + "  NoLP " + noLpFewerNodes + "  tie " + equalNodes + ".");
	}

	private static void writeCsv(List<BenchmarkResult> results, Options options) {
		Path csvFile = Paths.get(expandHome(options.csvPath));
		try {
			if (csvFile.getParent() != null)
				Files.createDirectories(csvFile.getParent());
			List<String> lines = new ArrayList<>();
			lines.add(csvRow(
					"instance",
					"spec",
					"iterations",
					"warmup",
					"common_args",
					"lp_proof",
					"lp_solution",
					"lp_best",
					"lp_bounds",
					"lp_gap",
					"lp_nodes",
					"lp_wall_seconds",
					"lp_search_seconds",
					"lp_stop",
					"lp_failed",
					"nolp_proof",
					"nolp_solution",
					"nolp_best",
					"nolp_bounds",
					"nolp_gap",
					"nolp_nodes",
					"nolp_wall_seconds",
					"nolp_search_seconds",
					"nolp_stop",
					"nolp_failed",
					"proof_status",
					"gap_improvement",
					"nodes_improvement"));
			for (BenchmarkResult result : results) {
				Aggregate lp = result.withLp;
				Aggregate noLp = result.withoutLp;
				lines.add(csvRow(
						result.displayName,
						result.spec,
						Integer.toString(options.iterations),
						Integer.toString(options.warmup),
						String.join(" ", options.solverArgs),
						lp.proofLabel(),
						lp.solutionLabel(),
						lp.bestLabel(),
						lp.boundsLabel(),
						lp.gapLabel(),
						formatCount(lp.avgNodes()),
						formatDouble(lp.avgWallSeconds()),
						formatDouble(lp.avgSearchSeconds()),
						compactStopping(lp.stoppingLabel()),
						Boolean.toString(lp.hasFailures()),
						noLp.proofLabel(),
						noLp.solutionLabel(),
						noLp.bestLabel(),
						noLp.boundsLabel(),
						noLp.gapLabel(),
						formatCount(noLp.avgNodes()),
						formatDouble(noLp.avgWallSeconds()),
						formatDouble(noLp.avgSearchSeconds()),
						compactStopping(noLp.stoppingLabel()),
						Boolean.toString(noLp.hasFailures()),
						proofStatus(lp, noLp),
						formatRelativeImprovement(lp.avgFiniteGap(), noLp.avgFiniteGap(), true),
						formatRelativeImprovement(lp.avgNodes(), noLp.avgNodes(), true)));
			}
			Files.write(csvFile, lines, StandardCharsets.UTF_8);
			System.out.println();
			System.out.println("CSV saved to " + csvFile);
		} catch (IOException e) {
			throw new RuntimeException("Cannot write benchmark CSV: " + csvFile, e);
		}
	}

	private static String expandHome(String value) {
		if (value.equals("~"))
			return System.getProperty("user.home");
		if (value.startsWith("~/"))
			return System.getProperty("user.home") + value.substring(1);
		return value;
	}

	private static String resolveCopDatasetDir() {
		for (String candidate : COP_DATASET_DIR_CANDIDATES) {
			String expanded = expandHome(candidate);
			if (Files.isDirectory(Paths.get(expanded)))
				return expanded;
		}
		return expandHome(COP_DATASET_DIR_CANDIDATES.get(0));
	}

	private static String format(double value) {
		return String.format(Locale.US, "%.3f", value);
	}

	private static String formatDouble(double value) {
		if (Double.isInfinite(value))
			return "inf";
		if (Double.isNaN(value))
			return "nan";
		return String.format(Locale.US, "%.6f", value);
	}

	private static String formatTime(double value) {
		return String.format(Locale.US, "%.2f", value);
	}

	private static String formatCount(double value) {
		double rounded = Math.rint(value);
		if (Math.abs(value - rounded) < 0.05d)
			return String.format(Locale.US, "%,d", (long) rounded);
		return String.format(Locale.US, "%,.1f", value);
	}

	private static String formatLong(long value) {
		if (value == Long.MIN_VALUE)
			return "-inf";
		if (value == Long.MAX_VALUE)
			return "+inf";
		return String.format(Locale.US, "%,d", value);
	}

	private static String compactStopping(String stopping) {
		if ("FULL_EXPLORATION".equals(stopping))
			return "full";
		if ("EXCEEDED_TIME".equals(stopping))
			return "time";
		if ("REACHED_GOAL".equals(stopping))
			return "goal";
		if ("ERROR".equals(stopping))
			return "error";
		return stopping.toLowerCase(Locale.ROOT);
	}

	private static String compareMetric(String label, double lpValue, double noLpValue, boolean lowerIsBetter) {
		if (Double.isInfinite(lpValue) || Double.isInfinite(noLpValue))
			return label + ": n/a";
		if (Math.abs(lpValue - noLpValue) < 1e-9)
			return label + ": x0.00";
		if (Math.abs(noLpValue) < 1e-12) {
			if (Math.abs(lpValue) < 1e-12)
				return label + ": x0.00";
			boolean improvedFromZero = lowerIsBetter ? lpValue < noLpValue : lpValue > noLpValue;
			return label + ": " + (improvedFromZero ? "x+inf" : "x-inf");
		}
		double improvement = lowerIsBetter ? (noLpValue - lpValue) / Math.abs(noLpValue) : (lpValue - noLpValue) / Math.abs(noLpValue);
		return String.format(Locale.US, "%s: x%+.2f", label, improvement);
	}

	private static String formatRelativeImprovement(double lpValue, double noLpValue, boolean lowerIsBetter) {
		if (Double.isInfinite(lpValue) || Double.isInfinite(noLpValue))
			return "";
		if (Math.abs(lpValue - noLpValue) < 1e-9)
			return "0.000000";
		if (Math.abs(noLpValue) < 1e-12) {
			if (Math.abs(lpValue) < 1e-12)
				return "0.000000";
			boolean improvedFromZero = lowerIsBetter ? lpValue < noLpValue : lpValue > noLpValue;
			return improvedFromZero ? "inf" : "-inf";
		}
		double improvement = lowerIsBetter ? (noLpValue - lpValue) / Math.abs(noLpValue) : (lpValue - noLpValue) / Math.abs(noLpValue);
		return String.format(Locale.US, "%.6f", improvement);
	}

	private static Map<String, String> runWorker(List<String> args) {
		Path metricsFile = null;
		try {
			metricsFile = Files.createTempFile("ace-benchmark-", ".metrics");
			List<String> command = new ArrayList<>();
			command.add(javaExecutable());
			command.addAll(forwardedJvmArgs());
			command.add("-cp");
			command.add(System.getProperty("java.class.path"));
			command.add("problems.BenchmarkLpVsNoLpWorker");
			command.add("--metrics=" + metricsFile.toAbsolutePath());
			command.addAll(args);
			Process process = new ProcessBuilder(command).redirectErrorStream(true).start();
			String output = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
			int exitCode = process.waitFor();
			Map<String, String> values = Files.exists(metricsFile) ? readMetrics(metricsFile) : failedMetrics("worker exited with code " + exitCode);
			if (exitCode != 0 && !values.containsKey("error") && !output.isBlank())
				values.put("error", sanitize(output));
			return values;
		} catch (InterruptedException e) {
			Thread.currentThread().interrupt();
			return failedMetrics("worker interrupted");
		} catch (IOException e) {
			return failedMetrics(e.getClass().getSimpleName() + ": " + e.getMessage());
		} finally {
			if (metricsFile != null) {
				try {
					Files.deleteIfExists(metricsFile);
				} catch (IOException ignored) {
				}
			}
		}
	}

	private static Map<String, String> readMetrics(Path metricsFile) throws IOException {
		Map<String, String> values = new LinkedHashMap<>();
		for (String line : Files.readAllLines(metricsFile, StandardCharsets.UTF_8)) {
			int index = line.indexOf('=');
			if (index <= 0)
				continue;
			values.put(line.substring(0, index), line.substring(index + 1));
		}
		return values;
	}

	private static Map<String, String> failedMetrics(String error) {
		Map<String, String> values = new LinkedHashMap<>();
		values.put("failed", "true");
		values.put("wallSeconds", "0");
		values.put("searchSeconds", "0");
		values.put("bestBound", "0");
		values.put("minBound", Long.toString(Long.MIN_VALUE));
		values.put("maxBound", Long.toString(Long.MAX_VALUE));
		values.put("nodes", "0");
		values.put("wrongDecisions", "0");
		values.put("foundSolutions", "0");
		values.put("provedOptimum", "false");
		values.put("stopping", "ERROR");
		values.put("error", sanitize(error));
		return values;
	}

	private static String javaExecutable() {
		Path javaHome = Paths.get(System.getProperty("java.home"), "bin", "java");
		return javaHome.toString();
	}

	private static List<String> forwardedJvmArgs() {
		return ManagementFactory.getRuntimeMXBean().getInputArguments().stream()
				.filter(arg -> arg.startsWith("-Xms") || arg.startsWith("-Xmx") || arg.equals("-ea") || arg.equals("-da"))
				.collect(Collectors.toList());
	}

	private static boolean parseBoolean(Map<String, String> values, String key, boolean defaultValue) {
		String value = values.get(key);
		return value == null ? defaultValue : Boolean.parseBoolean(value);
	}

	private static double parseDouble(Map<String, String> values, String key, double defaultValue) {
		String value = values.get(key);
		if (value == null || value.isEmpty())
			return defaultValue;
		try {
			return Double.parseDouble(value);
		} catch (NumberFormatException e) {
			return defaultValue;
		}
	}

	private static long parseLong(Map<String, String> values, String key, long defaultValue) {
		String value = values.get(key);
		if (value == null || value.isEmpty())
			return defaultValue;
		try {
			return Long.parseLong(value);
		} catch (NumberFormatException e) {
			return defaultValue;
		}
	}

	private static String sanitize(String text) {
		return text == null ? "" : text.replace('\n', ' ').replace('\r', ' ').trim();
	}

	private static String proofStatus(Aggregate lp, Aggregate noLp) {
		if (lp.alwaysProvedOptimum() && noLp.alwaysProvedOptimum())
			return "both";
		if (lp.alwaysProvedOptimum())
			return "lp_only";
		if (noLp.alwaysProvedOptimum())
			return "nolp_only";
		return "neither";
	}

	private static String csvRow(String... cells) {
		return Stream.of(cells).map(BenchmarkLpVsNoLp::csvCell).collect(Collectors.joining(","));
	}

	private static String csvCell(String value) {
		String cell = value == null ? "" : value;
		if (cell.contains(",") || cell.contains("\"") || cell.contains("\n") || cell.contains("\r"))
			return "\"" + cell.replace("\"", "\"\"") + "\"";
		return cell;
	}

	private static String fixedRow(String[] values, int[] widths, boolean[] rightAligned) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < values.length; i++) {
			if (i > 0)
				sb.append("  ");
			String value = values[i] == null ? "" : values[i];
			sb.append(rightAligned[i] ? padLeft(value, widths[i]) : padRight(value, widths[i]));
		}
		return sb.toString();
	}

	private static String rule(int[] widths) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < widths.length; i++) {
			if (i > 0)
				sb.append("  ");
			sb.append("-".repeat(Math.max(1, widths[i])));
		}
		return sb.toString();
	}

	private static String padLeft(String value, int width) {
		if (value.length() >= width)
			return value;
		return " ".repeat(width - value.length()) + value;
	}

	private static String padRight(String value, int width) {
		if (value.length() >= width)
			return value;
		return value + " ".repeat(width - value.length());
	}
}
