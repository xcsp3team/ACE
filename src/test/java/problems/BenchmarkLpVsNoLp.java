package problems;

import static solver.Solver.Stopping.FULL_EXPLORATION;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import main.Head;
import dashboard.Input;
import optimization.Optimizer;

/**
 * Benchmark runner comparing ACE with LP enabled and disabled on the same
 * optimization instances.
 *
 * The benchmark is proof-oriented: it highlights whether optimality is proved
 * within the same budget, the final objective gap, and the explored nodes.
 *
 * Usage examples:
 * ./gradlew benchmarkLpVsNoLp
 * ./gradlew benchmarkLpVsNoLp -PbenchmarkArgs="--iterations=1 --warmup=0 --arg=-t=30s --cop-dataset --limit=10"
 * ./gradlew benchmarkLpVsNoLp -PbenchmarkArgs="--arg=-t=20s ./examples/XCSP25/COP25/"
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
			"./examples/XCSP25/COP25",
			"./examples/XCSP25/COP25");

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

		RunMetrics(Mode mode, Head head) {
			this.mode = mode;
			this.wallSeconds = head.instanceStopwatch.wckTime() / 1000.0;
			if (head.solver == null) {
				this.failed = true;
				this.searchSeconds = 0.0;
				this.bestBound = 0L;
				this.nodes = 0L;
				this.wrongDecisions = 0L;
				this.foundSolutions = 0L;
				this.stopping = "ERROR";
				this.minBound = Long.MIN_VALUE;
				this.maxBound = Long.MAX_VALUE;
				this.provedOptimum = false;
				this.finiteGap = null;
				return;
			}
			this.failed = false;
			this.searchSeconds = head.solver.stats.times.searchWck / 1000.0;
			this.bestBound = head.solver.solutions.bestBound;
			this.nodes = head.solver.stats.nNodes;
			this.wrongDecisions = head.solver.stats.nWrongDecisions;
			this.foundSolutions = head.solver.solutions.found;
			this.stopping = head.solver.stopping == null ? "null" : head.solver.stopping.name();

			Optimizer optimizer = head.problem == null ? null : head.problem.optimizer;
			if (optimizer == null) {
				this.minBound = Long.MIN_VALUE;
				this.maxBound = Long.MAX_VALUE;
				this.provedOptimum = false;
				this.finiteGap = null;
				return;
			}
			this.minBound = optimizer.minBound;
			this.maxBound = optimizer.maxBound;
			this.provedOptimum = isOptimumProved(head, optimizer);
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
			} else if (arg.equals("--copdataset") || arg.equals("--cop-dataset")) {
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
		Head head = runResolutionSilently(tokens);
		return new RunMetrics(mode, head);
	}

	private static List<String> buildArgs(String resolved, List<String> commonArgs, Mode mode) {
		List<String> tokens = new ArrayList<>();
		tokens.add(resolved);
		tokens.add("-v=-1");
		tokens.add("-lp=" + mode.enabled);
		tokens.addAll(commonArgs);
		return tokens;
	}

	private static Head runResolutionSilently(List<String> args) {
		PrintStream previousOut = System.out;
		PrintStream previousErr = System.err;
		try (PrintStream silent = new PrintStream(OutputStream.nullOutputStream())) {
			System.setOut(silent);
			System.setErr(silent);
			Input.loadArguments(args.toArray(new String[0]));
			Head resolution = new Head();
			try {
				resolution.start();
				resolution.join();
			} catch (InterruptedException e) {
				Thread.currentThread().interrupt();
				throw new RuntimeException("Benchmark interrupted for args: " + args, e);
			}
			return resolution;
		} finally {
			System.setOut(previousOut);
			System.setErr(previousErr);
		}
	}

	private static String resolveSpec(String spec) {
		String expanded = expandHome(spec);
		Path path = Paths.get(expanded);
		if (Files.exists(path))
			return path.toString();
		if (expanded.endsWith(".xml.lzma"))
			return expanded;
		URL resource = Head.class.getResource(expanded.endsWith(".xml") || expanded.endsWith(".lzma") ? expanded : expanded + ".xml.lzma");
		return resource != null ? resource.getPath() : expanded;
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

	private static boolean isOptimumProved(Head head, Optimizer optimizer) {
		if (head.solver.solutions.found == 0)
			return false;
		if (head.solver.stopping == FULL_EXPLORATION)
			return true;
		return optimizer.minimization ? optimizer.minBound == head.solver.solutions.bestBound : optimizer.maxBound == head.solver.solutions.bestBound;
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
		if (Double.isInfinite(lpValue) && Double.isInfinite(noLpValue))
			return label + ": tie";
		if (Math.abs(lpValue - noLpValue) < 1e-9)
			return label + ": tie";
		boolean lpBetter = lowerIsBetter ? lpValue < noLpValue : lpValue > noLpValue;
		double better = lpBetter ? lpValue : noLpValue;
		double worse = lpBetter ? noLpValue : lpValue;
		String winner = lpBetter ? "LP" : "NoLP";
		if (better <= 0.0)
			return label + ": " + winner + " better";
		double ratio = worse / better;
		return String.format(Locale.US, "%s: %s (x%.2f)", label, winner, ratio);
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
