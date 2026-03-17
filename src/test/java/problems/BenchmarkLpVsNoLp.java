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
 * Benchmark runner comparing ACE with LP+reduced-cost fixing, LP-only and
 * NoLP on the same optimization instances.
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
		LP_WITH_RC(true, true, "LP+RC"),
		LP_ONLY(true, false, "LP"),
		LP_OFF(false, false, "NoLP");

		final boolean lpEnabled;
		final boolean reducedCostsEnabled;
		final String label;

		Mode(boolean lpEnabled, boolean reducedCostsEnabled, String label) {
			this.lpEnabled = lpEnabled;
			this.reducedCostsEnabled = reducedCostsEnabled;
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
		final long rootMinBound;
		final long rootMaxBound;
		final long nodes;
		final long wrongDecisions;
		final long foundSolutions;
		final boolean provedOptimum;
		final Long finiteGap;
		final String stopping;
		final boolean reducedCostsEnabled;
		final long reducedCostRounds;
		final long reducedCostTightenings;
		final long reducedCostValuesRemoved;
		final long reducedCostWipeouts;
		final long reducedCostReoptimizations;
		final long reducedCostImprovingReoptimizations;

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
			this.rootMinBound = parseLong(values, "rootMinBound", Long.MIN_VALUE);
			this.rootMaxBound = parseLong(values, "rootMaxBound", Long.MAX_VALUE);
			this.provedOptimum = parseBoolean(values, "provedOptimum", false);
			this.finiteGap = minBound != Long.MIN_VALUE && maxBound != Long.MAX_VALUE ? Math.max(0L, maxBound - minBound) : null;
			this.reducedCostsEnabled = parseBoolean(values, "reducedCostsEnabled", false);
			this.reducedCostRounds = parseLong(values, "reducedCostRounds", 0L);
			this.reducedCostTightenings = parseLong(values, "reducedCostTightenings", 0L);
			this.reducedCostValuesRemoved = parseLong(values, "reducedCostValuesRemoved", 0L);
			this.reducedCostWipeouts = parseLong(values, "reducedCostWipeouts", 0L);
			this.reducedCostReoptimizations = parseLong(values, "reducedCostReoptimizations", 0L);
			this.reducedCostImprovingReoptimizations = parseLong(values, "reducedCostImprovingReoptimizations", 0L);
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
		double reducedCostRounds;
		double reducedCostTightenings;
		double reducedCostValuesRemoved;
		double reducedCostWipeouts;
		double reducedCostReoptimizations;
		double reducedCostImprovingReoptimizations;
		long firstBestBound;
		long firstMinBound;
		long firstMaxBound;
		long firstRootMinBound;
		long firstRootMaxBound;
		boolean bestBoundConsistent = true;
		boolean boundsConsistent = true;
		boolean rootBoundsConsistent = true;
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
				firstRootMinBound = metrics.rootMinBound;
				firstRootMaxBound = metrics.rootMaxBound;
				firstStopping = metrics.stopping;
			} else {
				bestBoundConsistent &= firstBestBound == metrics.bestBound;
				boundsConsistent &= firstMinBound == metrics.minBound && firstMaxBound == metrics.maxBound;
				rootBoundsConsistent &= firstRootMinBound == metrics.rootMinBound && firstRootMaxBound == metrics.rootMaxBound;
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
			reducedCostRounds += metrics.reducedCostRounds;
			reducedCostTightenings += metrics.reducedCostTightenings;
			reducedCostValuesRemoved += metrics.reducedCostValuesRemoved;
			reducedCostWipeouts += metrics.reducedCostWipeouts;
			reducedCostReoptimizations += metrics.reducedCostReoptimizations;
			reducedCostImprovingReoptimizations += metrics.reducedCostImprovingReoptimizations;
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

		double avgReducedCostRounds() {
			return reducedCostRounds / runs;
		}

		double avgReducedCostTightenings() {
			return reducedCostTightenings / runs;
		}

		double avgReducedCostValuesRemoved() {
			return reducedCostValuesRemoved / runs;
		}

		double avgReducedCostWipeouts() {
			return reducedCostWipeouts / runs;
		}

		double avgReducedCostReoptimizations() {
			return reducedCostReoptimizations / runs;
		}

		double avgReducedCostImprovingReoptimizations() {
			return reducedCostImprovingReoptimizations / runs;
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

		String rootBoundsLabel() {
			if (!rootBoundsConsistent)
				return "varies";
			return formatLong(firstRootMinBound) + ".." + formatLong(firstRootMaxBound);
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
		final String family;
		final Aggregate withLpReducedCosts = new Aggregate(Mode.LP_WITH_RC);
		final Aggregate withLpOnly = new Aggregate(Mode.LP_ONLY);
		final Aggregate withoutLp = new Aggregate(Mode.LP_OFF);

		BenchmarkResult(String spec, String displayName) {
			this.spec = spec;
			this.displayName = displayName;
			this.family = familyName(displayName);
		}

		Aggregate aggregate(Mode mode) {
			if (mode == Mode.LP_WITH_RC)
				return withLpReducedCosts;
			if (mode == Mode.LP_ONLY)
				return withLpOnly;
			return withoutLp;
		}
	}

	public static void main(String[] args) {
		Options options = parseOptions(args);
		List<String> instances = collectInstances(options);
		System.out.println("Benchmark LP+RC vs LP vs NoLP");
		System.out.println("focus=proof-of-optimality gap nodes reduced-cost tightenings");
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
				result.aggregate(mode).add(metrics);
			}
		}
	}

	private static Mode[] orderedModes(int iteration) {
		Mode[] modes = Mode.values();
		Mode[] ordered = new Mode[modes.length];
		int shift = iteration % modes.length;
		for (int i = 0; i < modes.length; i++)
			ordered[i] = modes[(i + shift) % modes.length];
		return ordered;
	}

	private static RunMetrics runOne(String resolved, List<String> commonArgs, Mode mode) {
		List<String> tokens = buildArgs(resolved, commonArgs, mode);
		return new RunMetrics(mode, runWorker(tokens, mode));
	}

	private static List<String> buildArgs(String resolved, List<String> commonArgs, Mode mode) {
		List<String> tokens = new ArrayList<>();
		tokens.add(resolved);
		tokens.add("-v=-1");
		tokens.add("-lp=" + mode.lpEnabled);
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
		Aggregate lpRc = result.withLpReducedCosts;
		Aggregate lp = result.withLpOnly;
		Aggregate noLp = result.withoutLp;
		String[] headers = { "mode", "proof", "sol", "best", "bounds", "root", "gap", "nodes", "rcfix", "rcvals", "wall", "search", "stop" };
		int[] widths = { 6, 7, 5, 10, 17, 17, 10, 12, 10, 10, 8, 8, 6 };
		boolean[] rightAligned = { false, false, false, true, false, false, true, true, true, true, true, true, false };
		System.out.println(result.displayName);
		System.out.println(fixedRow(headers, widths, rightAligned));
		System.out.println(rule(widths));
		System.out.println(row(lpRc, widths, rightAligned));
		System.out.println(row(lp, widths, rightAligned));
		System.out.println(row(noLp, widths, rightAligned));
		System.out.println(comparisonLine("rc-vs-lp", lpRc, lp));
		System.out.println(comparisonLine("lp-vs-nolp", lp, noLp));
		System.out.println();
	}

	private static String row(Aggregate aggregate, int[] widths, boolean[] rightAligned) {
		String[] values = { aggregate.mode.label, aggregate.proofLabel(), aggregate.solutionLabel(), aggregate.bestLabel(), aggregate.boundsLabel(),
				aggregate.rootBoundsLabel(), aggregate.gapLabel(), formatCount(aggregate.avgNodes()), formatCount(aggregate.avgReducedCostTightenings()),
				formatCount(aggregate.avgReducedCostValuesRemoved()), formatTime(aggregate.avgWallSeconds()), formatTime(aggregate.avgSearchSeconds()),
				compactStopping(aggregate.stoppingLabel()) };
		return fixedRow(values, widths, rightAligned);
	}

	private static String comparisonLine(String label, Aggregate left, Aggregate right) {
		if (left.hasFailures() || right.hasFailures())
			return label + ": n/a (error)";
		String proof = proofStatus(label + " proof", left, right);
		String gap = compareMetric("gap", left.avgFiniteGap(), right.avgFiniteGap(), true);
		String nodes = compareMetric("nodes", left.avgNodes(), right.avgNodes(), true);
		return proof + "  " + gap + "  " + nodes;
	}

	private static void printGlobalSummary(List<BenchmarkResult> results) {
		int lpRcProved = 0;
		int lpProved = 0;
		int noLpProved = 0;
		int lpRcOnlyVsLp = 0;
		int lpOnlyVsRc = 0;
		int lpOnlyVsNoLp = 0;
		int noLpOnlyVsLp = 0;
		int lpRcBetterGapVsLp = 0;
		int lpBetterGapVsRc = 0;
		int equalGapRcVsLp = 0;
		int lpRcBetterNodesVsLp = 0;
		int lpBetterNodesVsRc = 0;
		int equalNodesRcVsLp = 0;
		int instanceWidth = Math.max("instance".length(),
				results.stream().map(result -> result.displayName.length()).max(Integer::compareTo).orElse(0));
		int familyWidth = Math.max("family".length(), results.stream().map(result -> result.family.length()).max(Integer::compareTo).orElse(0));
		String[] headers = { padRight("instance", instanceWidth), padRight("family", familyWidth), "LP+RC", "LP", "NoLP", "RC gap", "LP gap", "NoLP gap",
				"RC nodes", "LP nodes", "NoLP nodes", "RC fix", "RC vals" };
		int[] widths = { instanceWidth, familyWidth, 5, 4, 4, 10, 10, 10, 12, 12, 12, 10, 10 };
		boolean[] rightAligned = { false, false, false, false, false, true, true, true, true, true, true, true, true };

		System.out.println("Summary");
		System.out.println(fixedRow(headers, widths, rightAligned));
		System.out.println(rule(widths));
		for (BenchmarkResult result : results) {
			Aggregate lpRc = result.withLpReducedCosts;
			Aggregate lp = result.withLpOnly;
			Aggregate noLp = result.withoutLp;
			boolean lpRcOpt = lpRc.alwaysProvedOptimum();
			boolean lpOpt = lp.alwaysProvedOptimum();
			boolean noLpOpt = noLp.alwaysProvedOptimum();
			if (lpRcOpt)
				lpRcProved++;
			if (lpOpt)
				lpProved++;
			if (noLpOpt)
				noLpProved++;
			if (lpRcOpt && !lpOpt)
				lpRcOnlyVsLp++;
			if (!lpRcOpt && lpOpt)
				lpOnlyVsRc++;
			if (lpOpt && !noLpOpt)
				lpOnlyVsNoLp++;
			if (!lpOpt && noLpOpt)
				noLpOnlyVsLp++;

			double lpRcGap = lpRc.avgFiniteGap();
			double lpGap = lp.avgFiniteGap();
			double noLpGap = noLp.avgFiniteGap();
			double lpRcNodes = lpRc.avgNodes();
			double lpNodes = lp.avgNodes();
			double noLpNodes = noLp.avgNodes();
			if (!lpRc.hasFailures() && !lp.hasFailures()) {
				if (lpRcGap < lpGap)
					lpRcBetterGapVsLp++;
				else if (lpRcGap > lpGap)
					lpBetterGapVsRc++;
				else
					equalGapRcVsLp++;

				if (lpRcNodes < lpNodes)
					lpRcBetterNodesVsLp++;
				else if (lpRcNodes > lpNodes)
					lpBetterNodesVsRc++;
				else
					equalNodesRcVsLp++;
			}

			String[] values = { result.displayName, result.family, lpRc.proofLabel(), lp.proofLabel(), noLp.proofLabel(), lpRc.gapLabel(), lp.gapLabel(),
					noLp.gapLabel(), formatCount(lpRcNodes), formatCount(lpNodes), formatCount(noLpNodes),
					formatCount(lpRc.avgReducedCostTightenings()), formatCount(lpRc.avgReducedCostValuesRemoved()) };
			System.out.println(fixedRow(values, widths, rightAligned));
		}

		System.out.println();
		System.out.println("LP+RC proves optimum on " + lpRcProved + "/" + results.size() + " instance(s); LP on " + lpProved + "/" + results.size()
				+ "; NoLP on " + noLpProved + "/" + results.size() + ".");
		System.out.println("LP+RC-only proofs vs LP: " + lpRcOnlyVsLp + "  LP-only vs LP+RC: " + lpOnlyVsRc + ".");
		System.out.println("LP-only proofs vs NoLP: " + lpOnlyVsNoLp + "  NoLP-only vs LP: " + noLpOnlyVsLp + ".");
		System.out.println("Smaller final gap (LP+RC vs LP): LP+RC " + lpRcBetterGapVsLp + "  LP " + lpBetterGapVsRc + "  tie " + equalGapRcVsLp + ".");
		System.out.println(
				"Fewer explored nodes (LP+RC vs LP): LP+RC " + lpRcBetterNodesVsLp + "  LP " + lpBetterNodesVsRc + "  tie " + equalNodesRcVsLp + ".");
	}

	private static void writeCsv(List<BenchmarkResult> results, Options options) {
		Path csvFile = Paths.get(expandHome(options.csvPath));
		try {
			if (csvFile.getParent() != null)
				Files.createDirectories(csvFile.getParent());
			List<String> lines = new ArrayList<>();
			lines.add(csvRow(
					"instance",
					"family",
					"spec",
					"iterations",
					"warmup",
					"common_args",
					"lp_rc_proof",
					"lp_rc_solution",
					"lp_rc_best",
					"lp_rc_bounds",
					"lp_rc_root_bounds",
					"lp_rc_gap",
					"lp_rc_nodes",
					"lp_rc_wall_seconds",
					"lp_rc_search_seconds",
					"lp_rc_stop",
					"lp_rc_failed",
					"lp_rc_rounds",
					"lp_rc_tightenings",
					"lp_rc_values_removed",
					"lp_rc_wipeouts",
					"lp_rc_reoptimizations",
					"lp_rc_improving_reoptimizations",
					"lp_proof",
					"lp_solution",
					"lp_best",
					"lp_bounds",
					"lp_root_bounds",
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
					"nolp_root_bounds",
					"nolp_gap",
					"nolp_nodes",
					"nolp_wall_seconds",
					"nolp_search_seconds",
					"nolp_stop",
					"nolp_failed",
					"proof_status_rc_vs_lp",
					"proof_status_lp_vs_nolp",
					"gap_improvement_rc_vs_lp",
					"nodes_improvement_rc_vs_lp",
					"gap_improvement_lp_vs_nolp",
					"nodes_improvement_lp_vs_nolp"));
			for (BenchmarkResult result : results) {
				Aggregate lpRc = result.withLpReducedCosts;
				Aggregate lp = result.withLpOnly;
				Aggregate noLp = result.withoutLp;
				lines.add(csvRow(
						result.displayName,
						result.family,
						result.spec,
						Integer.toString(options.iterations),
						Integer.toString(options.warmup),
						String.join(" ", options.solverArgs),
						lpRc.proofLabel(),
						lpRc.solutionLabel(),
						lpRc.bestLabel(),
						lpRc.boundsLabel(),
						lpRc.rootBoundsLabel(),
						lpRc.gapLabel(),
						formatCount(lpRc.avgNodes()),
						formatDouble(lpRc.avgWallSeconds()),
						formatDouble(lpRc.avgSearchSeconds()),
						compactStopping(lpRc.stoppingLabel()),
						Boolean.toString(lpRc.hasFailures()),
						formatCount(lpRc.avgReducedCostRounds()),
						formatCount(lpRc.avgReducedCostTightenings()),
						formatCount(lpRc.avgReducedCostValuesRemoved()),
						formatCount(lpRc.avgReducedCostWipeouts()),
						formatCount(lpRc.avgReducedCostReoptimizations()),
						formatCount(lpRc.avgReducedCostImprovingReoptimizations()),
						lp.proofLabel(),
						lp.solutionLabel(),
						lp.bestLabel(),
						lp.boundsLabel(),
						lp.rootBoundsLabel(),
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
						noLp.rootBoundsLabel(),
						noLp.gapLabel(),
						formatCount(noLp.avgNodes()),
						formatDouble(noLp.avgWallSeconds()),
						formatDouble(noLp.avgSearchSeconds()),
						compactStopping(noLp.stoppingLabel()),
						Boolean.toString(noLp.hasFailures()),
						proofStatusForCsv(lpRc, lp),
						proofStatusForCsv(lp, noLp),
						formatRelativeImprovement(lpRc.avgFiniteGap(), lp.avgFiniteGap(), true),
						formatRelativeImprovement(lpRc.avgNodes(), lp.avgNodes(), true),
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
			return label + ": +0.00";
		if (Math.abs(noLpValue) < 1e-12) {
			if (Math.abs(lpValue) < 1e-12)
				return label + ": +0.00";
			boolean improvedFromZero = lowerIsBetter ? lpValue < noLpValue : lpValue > noLpValue;
			return label + ": " + (improvedFromZero ? "+inf" : "-inf");
		}
		double improvement = lowerIsBetter ? (noLpValue - lpValue) / Math.abs(noLpValue) : (lpValue - noLpValue) / Math.abs(noLpValue);
		return String.format(Locale.US, "%s: %+.2f", label, improvement);
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

	private static Map<String, String> runWorker(List<String> args, Mode mode) {
		Path metricsFile = null;
		try {
			metricsFile = Files.createTempFile("ace-benchmark-", ".metrics");
			List<String> command = new ArrayList<>();
			command.add(javaExecutable());
			command.addAll(forwardedJvmArgs());
			command.add("-D" + optimization.LPRelaxation.REDUCED_COSTS_PROPERTY + "=" + mode.reducedCostsEnabled);
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

	private static String proofStatus(String label, Aggregate left, Aggregate right) {
		if (left.alwaysProvedOptimum() && right.alwaysProvedOptimum())
			return label + ": both";
		if (left.alwaysProvedOptimum())
			return label + ": " + left.mode.label;
		if (right.alwaysProvedOptimum())
			return label + ": " + right.mode.label;
		return label + ": neither";
	}

	private static String proofStatusForCsv(Aggregate left, Aggregate right) {
		if (left.alwaysProvedOptimum() && right.alwaysProvedOptimum())
			return "both";
		if (left.alwaysProvedOptimum())
			return left.mode.label.toLowerCase(Locale.ROOT).replace("+", "_");
		if (right.alwaysProvedOptimum())
			return right.mode.label.toLowerCase(Locale.ROOT).replace("+", "_");
		return "neither";
	}

	private static String familyName(String displayName) {
		int dash = displayName.indexOf('-');
		int underscore = displayName.indexOf('_');
		int cut = dash >= 0 ? dash : underscore;
		if (cut < 0)
			return displayName;
		if (underscore >= 0 && (dash < 0 || underscore < dash))
			cut = underscore;
		return cut == 0 ? displayName : displayName.substring(0, cut);
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
