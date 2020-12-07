/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package solver;

import static dashboard.Output.CPU;
import static dashboard.Output.MEM;
import static dashboard.Output.N_BUILT_BRANCHES;
import static dashboard.Output.N_EFFECTIVE_SINGLETON_TESTS;
import static dashboard.Output.N_FOUND_SINGLETONS;
import static dashboard.Output.N_SINGLETON_TESTS;
import static dashboard.Output.STOP;
import static dashboard.Output.SUM_BRANCH_SIZES;
import static dashboard.Output.WCK;

import java.text.NumberFormat;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.xcsp.common.Types.TypeFramework;

import dashboard.Arguments;
import dashboard.Output;
import interfaces.Observers.ObserverRuns;
import interfaces.Observers.ObserverSearch;
import learning.IpsRecorderForEquivalence;
import learning.ReductionOperator;
import main.Head;
import problem.Features.MapAtt;
import propagation.Forward;
import propagation.GAC;
import propagation.GIC.GIC4;
import propagation.SAC;
import propagation.SAC.SACGreedy;
import utility.Enums.EStopping;
import utility.Enums.TypeOutput;
import utility.Kit;
import utility.Kit.Stopwatch;
import variables.Variable;

/**
 * This class allows gathering all statistics of a given solver.
 */
public abstract class Statistics implements ObserverRuns, ObserverSearch {

	private static NumberFormat nformat = NumberFormat.getInstance();

	/*************************************************************************
	 ***** Interfaces
	 *************************************************************************/

	@Override
	public final void beforePreprocessing() {
		stopwatch.start();
		if (solver instanceof Solver && (((Solver) solver).nogoodRecorder != null))
			nPreproAddedNogoods = (((Solver) solver).nogoodRecorder).nNogoods;
		nPreproAddedCtrs = solver.problem.constraints.length;
	}

	@Override
	public final void afterPreprocessing() {
		preproWck += stopwatch.wckTime();
		if (solver instanceof Solver && (((Solver) solver).nogoodRecorder != null))
			nPreproAddedNogoods = (((Solver) solver).nogoodRecorder).nNogoods - nPreproAddedNogoods;
		nPreproAddedCtrs = solver.problem.constraints.length - nPreproAddedCtrs;
		nPreproRemovedValues = Variable.nRemovedValuesFor(solver.problem.variables);
		nPreproRemovedTuples = solver.propagation.nTuplesRemoved;
		nPreproInconsistencies = solver.stopping == EStopping.FULL_EXPLORATION ? 1 : 0;
	}

	@Override
	public final void beforeSolving() {
		stopwatch.start();
	}

	@Override
	public final void afterSolving() {
		solvingWck += stopwatch.wckTime();
	}

	@Override
	public void afterRun() {
		searchWck = stopwatch.wckTime();
	}

	public void onAssignment(Variable x) {
		nNodes++;
		if (x.dom.size() > 1)
			nDecisions++;
		// nAssignments++; done elsewhere
	}

	public void onRefutation(Variable x) {
		if (x.dom.size() > 1) {
			nNodes++;
			nDecisions++;
		}
	}

	/*************************************************************************
	 ***** Fields and Methods
	 *************************************************************************/

	public final Solver solver;

	public final Stopwatch stopwatch = new Stopwatch();

	public long nNodes = 1, nDecisions, nWrongDecisions, nBacktracks, nAssignments, nFailedAssignments;

	public long nPreproRemovedValues, nPreproRemovedTuples, nPreproAddedCtrs, nPreproAddedNogoods, nPreproInconsistencies;

	public long solvingWck, preproWck, searchWck, firstSolWck, firstSolCpu, lastSolWck, lastSolCpu;

	private long tmpNbAssignments, tmpNbBacktracks, tmpNbFailedAssignments;

	public Statistics(Solver solver) {
		this.solver = solver;
	}

	public long numberSafe() {
		return nNodes + nAssignments + nBacktracks;
	}

	public void store() {
		tmpNbAssignments = nAssignments;
		tmpNbFailedAssignments = nFailedAssignments;
		tmpNbBacktracks = nBacktracks;
	}

	public void restore() {
		nAssignments = tmpNbAssignments;
		nFailedAssignments = tmpNbFailedAssignments;
		nBacktracks = tmpNbBacktracks;
	}

	public final long nEffectiveFilterings() {
		return solver.problem.features.nEffectiveFilterings;
	}

	public final long nRevisions() {
		return solver.propagation instanceof Forward ? ((Forward) solver.propagation).reviser.nRevisions : 0;
	}

	public final long nUselessRevisions() {
		return solver.propagation instanceof Forward ? ((Forward) solver.propagation).reviser.nUselessRevisions : 0;
	}

	public final long nSingletonTests() {
		return solver.propagation.nSingletonTests;
	}

	public final long nEffectiveSingletonTests() {
		return solver.propagation.nEffectiveSingletonTests;
	}

	public void manageSolution() {
		long cpu = solver.head.stopwatch.cpuTime(), wck = solver.head.instanceStopwatch.wckTime();
		if (solver.solManager.found == 1) {
			firstSolCpu = cpu;
			firstSolWck = wck;
		}
		lastSolCpu = cpu;
		lastSolWck = wck;
	}

	public final MapAtt preproAttributes() {
		MapAtt m = new MapAtt("Preprocessing");
		m.put("eff", nEffectiveFilterings());
		m.putIf("revisions", "(" + nRevisions() + ",useless=" + nUselessRevisions() + ")", nRevisions() > 0);
		if (solver.propagation instanceof GAC)
			m.put("nACremovedValues", ((GAC) (solver.propagation)).nPreproRemovals);
		m.put("nTotalRemovedValues", nPreproRemovedValues);
		m.put("inconsistency", nPreproInconsistencies > 0);
		m.separator();
		if (nPreproRemovedTuples > 0 || nPreproAddedNogoods > 0 || nPreproAddedCtrs > 0) {
			m.put("nRemovedTuples", nPreproRemovedTuples);
			m.put("nNogoods", nPreproAddedNogoods);
			m.put("nAddedCtrs", nPreproAddedCtrs);
			m.separator();
		}
		if (nSingletonTests() > 0) {
			m.put(N_SINGLETON_TESTS, nSingletonTests());
			m.put(N_EFFECTIVE_SINGLETON_TESTS, nEffectiveSingletonTests());
			if (solver.propagation instanceof SAC)
				m.put(N_FOUND_SINGLETONS, ((SAC) (solver.propagation)).nFoundSingletons);
			if (solver.propagation instanceof SACGreedy) {
				m.put(N_BUILT_BRANCHES, ((SACGreedy) (solver.propagation)).nBranchesBuilt);
				m.put(SUM_BRANCH_SIZES, ((SACGreedy) (solver.propagation)).sumBranchSizes);
			}
			m.separator();
		}
		if (solver.solManager.found > 0) {
			m.put("foundSolutions", solver.solManager.found);
			m.put("firstSolCpu", firstSolCpu / 1000.0);
			m.separator();
		}
		m.put(WCK, preproWck / 1000.0);
		m.put(CPU, solver.head.stopwatch.cpuTimeInSeconds());

		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	public abstract MapAtt runAttributes();

	public abstract MapAtt cumulatedAttributes();

	// private boolean statMouny = true;

	public MapAtt globalAttributes() {
		MapAtt m = cumulatedAttributes();
		// m.put(EXPIRED_TIME, solver.rs.isTimeExpiredForCurrentInstance());
		// m.put(TOTAL_EXPLORATION, solver.isFullExploration());
		m.put(STOP, solver.stopping == null ? "no" : solver.stopping.toString());
		m.put("wrong", solver.stats.nWrongDecisions);
		// if (statMouny && solver.propagation instanceof ACPartial) {
		// int[] t = ((ACPartial) solver.propagation).statistics;
		// map.put("nbWOs", t[0] + ""); map.put("nbFPs", t[1] + ""); map.put("avgWOs", t[2] + ""); map.put("avgFPs", t[3] + ""); }
		if (solver.solManager.found > 0) {
			if (solver.problem.settings.framework != TypeFramework.CSP) {
				m.put("bestBound", solver.solManager.bestBound);
				m.put("bestBoundWck", lastSolWck / 1000.0);
				m.put("bestBoundCpu", lastSolCpu / 1000.0);
			}
			m.put("foundSolutions", solver.solManager.found);
			m.put("firstSolCpu", firstSolCpu / 1000.0);
			m.separator();
		}
		m.put(WCK, solver.head.instanceStopwatch.wckTimeInSeconds());
		m.put(CPU, solver.head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	/*************************************************************************
	 ***** StatisticsBacktrack
	 *************************************************************************/

	public static final class StatisticsBacktrack extends Statistics {

		protected Solver solver;

		public StatisticsBacktrack(Solver solver) {
			super(solver);
			this.solver = solver;
		}

		@Override
		public MapAtt runAttributes() {
			MapAtt m = new MapAtt("Run");
			m.put("run", solver.restarter.numRun);
			m.put("dpt", solver.minDepth + ".." + solver.maxDepth);
			m.put("eff", nEffectiveFilterings());
			m.put("wrg", nWrongDecisions);
			if (Kit.memory() > 10000000000L)
				m.put(Output.MEM, Kit.memoryInMb());
			m.put(Output.WCK, stopwatch.wckTimeInSeconds());
			if (solver.nogoodRecorder != null)
				m.putWhenPositive("ngd", solver.nogoodRecorder.nNogoods);
			if (solver.solManager.found > 0) {
				if (solver.problem.settings.framework == TypeFramework.CSP)
					m.put("nSols", solver.solManager.found);
				else {
					if (solver.problem.optimizer.minBound == 0 || solver.problem.optimizer.minBound == Long.MIN_VALUE)
						m.put("bnd", nformat.format(solver.solManager.bestBound));
					else
						m.put("bnds", solver.problem.optimizer.stringBounds());
					// m.put("bnd", nformat.format(solver.solManager.bestBound));
				}
			}
			if (solver.head.control.general.verbose <= 1)
				return m;
			m.separator();
			m.put("decs", nDecisions);
			m.put("backs", nBacktracks);
			m.put("failed", nFailedAssignments);
			m.putIf("revisions", "(" + nRevisions() + ",useless=" + nUselessRevisions() + ")", nRevisions() > 0);
			if (nSingletonTests() > 0) { // solver.getPreproPropagationTechnique() instanceof SingletonArcConsistency) {
				m.put(Output.N_SINGLETON_TESTS, nSingletonTests());
				m.put(Output.N_EFFECTIVE_SINGLETON_TESTS, nEffectiveSingletonTests());
			}
			if (Kit.memory() > 10000000000L)
				m.put(Output.MEM, Kit.memoryInMb());
			m.separator();
			if (solver.ipsRecorder != null && solver.ipsRecorder instanceof IpsRecorderForEquivalence && !solver.ipsRecorder.stopped) {
				IpsRecorderForEquivalence learner = (IpsRecorderForEquivalence) solver.ipsRecorder;
				m.put(Output.MAP_SIZE, learner.getMapSize());
				m.put(Output.N_INFERENCES, learner.nInferences);
				// map.put("nbInferredSolutions", solutionCounter.nbInferredSolutions );
				m.put(Output.N_TOO_LARGE_KEYS, learner.nTooLargeKeys);
			}
			if (solver.ipsRecorder != null) {
				ReductionOperator ro = solver.ipsRecorder.reductionOperator;
				// DecimalFormat df = new DecimalFormat("###.##",new DecimalFormatSymbols(Locale.ENGLISH));
				m.put(Output.N_SELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbSEliminableVariables()));
				m.put(Output.N_RELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbREliminableVariables()));
				m.put(Output.N_IELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbIEliminableVariables()));
				m.put(Output.N_DELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbDEliminableVariables()));
				m.put(Output.N_PELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbPEliminableVariables()));
				m.separator();
			}
			return m;
		}

		@Override
		public MapAtt cumulatedAttributes() {
			MapAtt m = new MapAtt("Global");
			m.put("eff", nEffectiveFilterings());
			m.putIf("revisions", "(" + nRevisions() + ",useless=" + nUselessRevisions() + ")", nRevisions() > 0);
			if (nSingletonTests() > 0) { // solver.getPreproPropagationTechnique() instanceof SingletonArcConsistency) {
				m.put(Output.N_SINGLETON_TESTS, nSingletonTests());
				m.put(Output.N_EFFECTIVE_SINGLETON_TESTS, nEffectiveSingletonTests());
			}

			if (solver.nogoodRecorder != null)
				m.putWhenPositive("nogoods", solver.nogoodRecorder.nNogoods);
			m.separator();
			return m;
		}
	}

	/*************************************************************************
	 ***** StatisticsMultiResolution
	 *************************************************************************/

	public static abstract class StatisticsMultiResolution {

		public abstract void update(boolean crashed);

		public abstract void outputGlobalStatistics();

		public static StatisticsMultiResolution buildFor(final Head resolution) {
			if (Arguments.nInstancesToSolve > 1)
				return new ActiveStatisticsMultiResolution(resolution);
			return new VoidStatisticsMultiResolution();
		}

		private static class VoidStatisticsMultiResolution extends StatisticsMultiResolution {

			@Override
			public void update(boolean crashed) {
			}

			@Override
			public void outputGlobalStatistics() {
			}

		}

		private static class ActiveStatisticsMultiResolution extends StatisticsMultiResolution {

			private Head resolution;

			/**
			 * The statistics of (proved) satisfiable instances. Interesting when there are more than 1 instance to be solved.
			 */
			private QuickStatistics[] satStatistics;

			/**
			 * The statistics of (proved) unsatisfiable instances. Interesting when there are more than 1 instance to be solved.
			 */
			private QuickStatistics[] unsatStatistics;

			/**
			 * The statistics of instances whose consistency is unknown. Interesting when there are more than 1 instance to be solved.
			 */
			private QuickStatistics[] unknownStatistics;

			/**
			 * The statistics of instances for which time has expired. Interesting when there are more than 1 instance to be solved.
			 */
			private QuickStatistics[] expiredStatistics;

			/**
			 * The statistics of all instances.
			 */
			private QuickStatistics[] allStatistics;

			private QuickStatistics[] crashedStatistics;

			/**
			 * Some statistical measures (including the number of constraint checks and the cpu time) are gathered (in case there are several instances to
			 * solve).
			 */
			private class QuickStatistics {
				private TypeOutput outputElement;

				private int nbTreatedInstances;
				private long preproWckTime, searchWckTime, allCpuTime;
				private long sumOfNbSingletonTests, sumOfNbEffectiveSingletonTests;
				private long sumOfNbPropagations;
				private long sumOfNbAssignments, sumOfNbFailedAssignments;
				private long sumOfNbSolutions;
				private long nbPreproValuesRemoved, nbPreproTuplesRemoved;
				private int nbPreproInconsistencies;
				private int nbSuccesses;
				private long[] durationsToRunSolver;
				private long memory;
				private int[] nbRemovedValues;
				private long nbFilterCallsSTR;
				private double sumTableProportionsSTR, sumTableSizesSTR;
				private long nbVals, nbUnks, nbUnksAfterAC, nbTests, wcks, minWck = Long.MAX_VALUE, maxWck = Long.MIN_VALUE, nbITestRestor;

				QuickStatistics(int level, TypeOutput outputElement) {
					this.outputElement = outputElement;
				}

				void updateStatisticsWith(Statistics statistics) {
					nbTreatedInstances++;
					preproWckTime += statistics.preproWck;
					searchWckTime += statistics.searchWck;

					// if (durationsToRunSolver != null)
					// durationsToRunSolver[nbTreatedInstances - 1] =
					// statistics.getDurationToRunSolver();
					sumOfNbSingletonTests += statistics.nSingletonTests();
					sumOfNbEffectiveSingletonTests += statistics.nEffectiveSingletonTests();

					sumOfNbPropagations = statistics.nEffectiveFilterings();
					sumOfNbAssignments += statistics.nAssignments;
					sumOfNbFailedAssignments += statistics.nFailedAssignments;
					sumOfNbSolutions += statistics.solver.solManager.found;

					nbPreproValuesRemoved += statistics.nPreproRemovedValues;
					nbPreproTuplesRemoved += statistics.nPreproRemovedTuples;
					nbPreproInconsistencies += statistics.nPreproInconsistencies;
					memory += Kit.memory();

					if (resolution.solver.propagation instanceof GIC4) {
						nbVals += ((GIC4) resolution.solver.propagation).nVals;
						nbUnks += ((GIC4) resolution.solver.propagation).nUnks;
						nbUnksAfterAC += ((GIC4) resolution.solver.propagation).nUnksAfterAC;
						nbTests += ((GIC4) resolution.solver.propagation).nTests;
						wcks += ((GIC4) resolution.solver.propagation).wck;
						minWck = Math.min(minWck, ((GIC4) resolution.solver.propagation).wck);
						maxWck = Math.max(maxWck, ((GIC4) resolution.solver.propagation).wck);
						nbITestRestor += ((GIC4) resolution.solver.propagation).nItestsRestor;
					}
				}

				void updateForMedian(long durationToRunSolver, boolean success) {
					if (durationsToRunSolver == null)
						durationsToRunSolver = new long[Arguments.nInstancesToSolve];
					if (success) {
						durationsToRunSolver[nbTreatedInstances - 1] = durationToRunSolver;
						nbSuccesses++;
					} else
						durationsToRunSolver[nbTreatedInstances - 1] = Long.MAX_VALUE;
				}

				long computeMedian() {
					int nbInstances = Arguments.nInstancesToSolve;
					if (nbSuccesses < nbInstances / 2 + 1)
						return -1;
					Arrays.sort(durationsToRunSolver);
					StringBuilder sb = new StringBuilder();
					for (int i = 0; i < durationsToRunSolver.length; i++)
						sb.append(durationsToRunSolver[i] + " ");
					// System.out.println("\t\t\tmedian= '" + sb + "'");
					if (nbInstances % 2 == 0)
						return (durationsToRunSolver[nbInstances / 2] + durationsToRunSolver[nbInstances / 2 - 1]) / 2;
					return durationsToRunSolver[nbInstances / 2];
				}

				public Map<String, Object> getMapOfCumulatedAttributes() {
					Map<String, Object> map = new LinkedHashMap<>();
					map.put(Output.N_INSTANCES, nbTreatedInstances);
					if (nbTreatedInstances != 0) {
						map.put(Output.PREPRO_WCK_TIME, (preproWckTime / nbTreatedInstances));
						map.put(Output.SEARCH_WCK_TIME, (searchWckTime / nbTreatedInstances));
						map.put(Output.SOLVING_CPU_TIME, (allCpuTime / nbTreatedInstances));
						if (durationsToRunSolver != null)
							map.put(Output.MEDIAN_CPU_TIME, computeMedian());

						if (sumOfNbSingletonTests != 0)
							map.put(Output.N_SINGLETON_TESTS, (sumOfNbSingletonTests / nbTreatedInstances));
						if (sumOfNbEffectiveSingletonTests != 0)
							map.put(Output.N_EFFECTIVE_SINGLETON_TESTS, (sumOfNbEffectiveSingletonTests / nbTreatedInstances));

						map.put(Output.N_EFFECTIVE_FILTERINGS, (sumOfNbPropagations / nbTreatedInstances));
						map.put(Output.N_ASSIGNMENTS, (sumOfNbAssignments / (double) nbTreatedInstances));
						map.put(Output.N_FAILED_ASSIGNMENTS, sumOfNbFailedAssignments);
						map.put(Output.N_FOUND_SOLUTIONS, (sumOfNbSolutions / (double) nbTreatedInstances));
						map.put(Output.N_REMOVED_VALUES, (nbPreproValuesRemoved / (double) nbTreatedInstances));
						map.put(Output.N_REMOVED_TUPLES, (nbPreproTuplesRemoved / (double) nbTreatedInstances));
						map.put(Output.N_FILTER_CALLS, nbFilterCallsSTR / (double) nbTreatedInstances);
						map.put(Output.AVG_TABLE_PROPORTION, sumTableProportionsSTR / nbTreatedInstances);
						map.put(Output.AVG_TABLE_SIZE, sumTableSizesSTR / nbTreatedInstances);
						map.put(Output.CPU, resolution.stopwatch.cpuTime() / (double) nbTreatedInstances);
						map.put(Output.MEM, (long) (memory / (double) nbTreatedInstances));

						if (resolution.control.experimental.helene)
							map.put("NbRemovedValues", Kit.join(nbRemovedValues, ";"));

						if (outputElement == TypeOutput.UNSAT)
							map.put(Output.N_PREPRO_INCONSISTENCIES, nbPreproInconsistencies);

						if (resolution.control.experimental.helene) {
							map.put("nbVals", nbVals / (double) nbTreatedInstances);
							map.put("nbUnks", nbUnks / (double) nbTreatedInstances);
							map.put("nbUnksAfterAC", nbUnksAfterAC / (double) nbTreatedInstances);
							map.put("nbTests", nbTests / (double) nbTreatedInstances);
							map.put("wck", wcks / (double) nbTreatedInstances);
							map.put("minWck", minWck);
							map.put("maxWck", maxWck);
							map.put("nbITestRestor", nbITestRestor / (double) nbTreatedInstances);
						}

					}
					return map;
				}

				void display() {
					Set<Entry<String, Object>> set = getMapOfCumulatedAttributes().entrySet();
					resolution.output.record(outputElement, set, null);
					System.out.println(outputElement);
					set.forEach(e -> System.out.println("\t" + e.getKey() + " : " + e.getValue()));
				}
			}

			public ActiveStatisticsMultiResolution(Head resolution) {
				this.resolution = resolution;
				int nbAbstractionLevels = 0;
				if (Arguments.nInstancesToSolve > 1) {
					satStatistics = new QuickStatistics[nbAbstractionLevels + 1];
					for (int i = 0; i < satStatistics.length; i++)
						satStatistics[i] = new QuickStatistics(i, TypeOutput.SAT);
					unsatStatistics = new QuickStatistics[nbAbstractionLevels + 1];
					for (int i = 0; i < unsatStatistics.length; i++)
						unsatStatistics[i] = new QuickStatistics(i, TypeOutput.UNSAT);
					unknownStatistics = new QuickStatistics[nbAbstractionLevels + 1];
					for (int i = 0; i < unknownStatistics.length; i++)
						unknownStatistics[i] = new QuickStatistics(i, TypeOutput.UNKNOWN);
					expiredStatistics = new QuickStatistics[nbAbstractionLevels + 1];
					for (int i = 0; i < expiredStatistics.length; i++)
						expiredStatistics[i] = new QuickStatistics(i, TypeOutput.EXPIRED);
					allStatistics = new QuickStatistics[nbAbstractionLevels + 1];
					for (int i = 0; i < allStatistics.length; i++)
						allStatistics[i] = new QuickStatistics(i, TypeOutput.ALL);
					crashedStatistics = new QuickStatistics[nbAbstractionLevels + 1];
					for (int i = 0; i < crashedStatistics.length; i++)
						crashedStatistics[i] = new QuickStatistics(i, TypeOutput.CRASHED);
				}
			}

			@Override
			public void update(boolean crashed) {
				if (crashed)
					crashedStatistics[0].nbTreatedInstances++;
				else {
					if (resolution.solver == null || resolution.solver.stats == null)
						return;
					Statistics stats = resolution.solver.stats;
					if (resolution.isTimeExpiredForCurrentInstance())
						expiredStatistics[0].updateStatisticsWith(stats);
					else if (stats.solver.solManager.found > 0)
						satStatistics[0].updateStatisticsWith(stats);
					else if (resolution.solver.isFullExploration())
						unsatStatistics[0].updateStatisticsWith(stats);
					else
						unknownStatistics[0].updateStatisticsWith(stats);
					allStatistics[0].updateStatisticsWith(stats);
					allStatistics[0].updateForMedian(stats.solvingWck,
							!resolution.isTimeExpiredForCurrentInstance() && (stats.solver.solManager.found > 0 || resolution.solver.isFullExploration()));
				}
			}

			@Override
			public void outputGlobalStatistics() {
				for (int i = 0; i < expiredStatistics.length; i++) {
					expiredStatistics[i].display();
					satStatistics[i].display();
					unsatStatistics[i].display();
					unknownStatistics[i].display();
					allStatistics[i].display();
					crashedStatistics[i].display();
				}
			}
		}
	}

}