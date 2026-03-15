package problems;

import static solver.Solver.Stopping.FULL_EXPLORATION;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import dashboard.Input;
import main.Head;
import optimization.Optimizer;

public final class BenchmarkLpVsNoLpWorker {

	public static void main(String[] args) throws IOException {
		WorkerOptions options = parseOptions(args);
		Map<String, String> metrics = runOne(options.solverArgs);
		writeMetrics(options.metricsFile, metrics);
	}

	private static WorkerOptions parseOptions(String[] args) {
		WorkerOptions options = new WorkerOptions();
		for (String arg : args) {
			if (arg.startsWith("--metrics="))
				options.metricsFile = Paths.get(arg.substring("--metrics=".length()));
			else
				options.solverArgs.add(arg);
		}
		if (options.metricsFile == null)
			throw new IllegalArgumentException("Missing --metrics=...");
		return options;
	}

	private static Map<String, String> runOne(List<String> solverArgs) {
		PrintStream previousOut = System.out;
		PrintStream previousErr = System.err;
		try (PrintStream silent = new PrintStream(OutputStream.nullOutputStream())) {
			System.setOut(silent);
			System.setErr(silent);
			Input.loadArguments(solverArgs.toArray(new String[0]));
			Head resolution = new Head();
			try {
				resolution.start();
				resolution.join();
				return collectMetrics(resolution);
			} catch (InterruptedException e) {
				Thread.currentThread().interrupt();
				return failedMetrics("worker interrupted");
			}
		} catch (Throwable t) {
			return failedMetrics(t.getClass().getSimpleName() + ": " + t.getMessage());
		} finally {
			System.setOut(previousOut);
			System.setErr(previousErr);
		}
	}

	private static Map<String, String> collectMetrics(Head head) {
		Map<String, String> values = new LinkedHashMap<>();
		values.put("failed", Boolean.toString(head.solver == null));
		values.put("wallSeconds", Double.toString(head.instanceStopwatch.wckTime() / 1000.0));
		if (head.solver == null) {
			values.put("searchSeconds", "0");
			values.put("bestBound", "0");
			values.put("minBound", Long.toString(Long.MIN_VALUE));
			values.put("maxBound", Long.toString(Long.MAX_VALUE));
			values.put("nodes", "0");
			values.put("wrongDecisions", "0");
			values.put("foundSolutions", "0");
			values.put("provedOptimum", "false");
			values.put("stopping", "ERROR");
			return values;
		}

		values.put("searchSeconds", Double.toString(head.solver.stats.times.searchWck / 1000.0));
		values.put("bestBound", Long.toString(head.solver.solutions.bestBound));
		values.put("nodes", Long.toString(head.solver.stats.nNodes));
		values.put("wrongDecisions", Long.toString(head.solver.stats.nWrongDecisions));
		values.put("foundSolutions", Long.toString(head.solver.solutions.found));
		values.put("stopping", head.solver.stopping == null ? "null" : head.solver.stopping.name());

		Optimizer optimizer = head.problem == null ? null : head.problem.optimizer;
		if (optimizer == null) {
			values.put("minBound", Long.toString(Long.MIN_VALUE));
			values.put("maxBound", Long.toString(Long.MAX_VALUE));
			values.put("provedOptimum", "false");
			return values;
		}

		values.put("minBound", Long.toString(optimizer.minBound));
		values.put("maxBound", Long.toString(optimizer.maxBound));
		values.put("provedOptimum", Boolean.toString(isOptimumProved(head, optimizer)));
		return values;
	}

	private static boolean isOptimumProved(Head head, Optimizer optimizer) {
		if (head.solver.solutions.found == 0)
			return false;
		if (head.solver.stopping == FULL_EXPLORATION)
			return true;
		return optimizer.minimization ? optimizer.minBound == head.solver.solutions.bestBound : optimizer.maxBound == head.solver.solutions.bestBound;
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
		values.put("error", error == null ? "" : error);
		return values;
	}

	private static void writeMetrics(Path file, Map<String, String> metrics) throws IOException {
		List<String> lines = new ArrayList<>();
		for (Map.Entry<String, String> entry : metrics.entrySet())
			lines.add(entry.getKey() + "=" + entry.getValue());
		Files.write(file, lines, StandardCharsets.UTF_8);
	}

	private static final class WorkerOptions {
		Path metricsFile;
		final List<String> solverArgs = new ArrayList<>();
	}
}
