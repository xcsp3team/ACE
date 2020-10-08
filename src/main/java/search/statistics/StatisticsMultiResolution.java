/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search.statistics;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import dashboard.Arguments;
import dashboard.Output;
import executables.Resolution;
import propagation.order1.inverse.GIC4;
import utility.Enums.TypeOutput;
import utility.Kit;

public abstract class StatisticsMultiResolution {

	public abstract void update(boolean crashed);

	public abstract void outputGlobalStatistics();

	public static StatisticsMultiResolution build(final Resolution resolution) {
		return Arguments.nInstancesToSolve > 1 ? new ActiveStatisticsMultiResolution(resolution) : new VoidStatisticsMultiResolution();
	}

	private static class VoidStatisticsMultiResolution extends StatisticsMultiResolution {

		@Override
		public void update(boolean crashed) {}

		@Override
		public void outputGlobalStatistics() {}

	}

	private static class ActiveStatisticsMultiResolution extends StatisticsMultiResolution {

		private Resolution resolution;

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
			private long sumOfNbConstraintChecks;
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
				if (resolution.problem.stuff.nFilterCallsSTR > 0) {
					nbFilterCallsSTR += resolution.problem.stuff.nFilterCallsSTR;
					sumTableProportionsSTR += resolution.problem.stuff.sumTableProportionsSTR / resolution.problem.stuff.nFilterCallsSTR;
					sumTableSizesSTR += resolution.problem.stuff.sumTableSizesSTR / resolution.problem.stuff.nFilterCallsSTR;
				}

				nbTreatedInstances++;
				preproWckTime += statistics.preproWck;
				searchWckTime += statistics.searchWck;

				// if (durationsToRunSolver != null)
				// durationsToRunSolver[nbTreatedInstances - 1] =
				// statistics.getDurationToRunSolver();
				sumOfNbSingletonTests += statistics.nSingletonTests();
				sumOfNbEffectiveSingletonTests += statistics.nEffectiveSingletonTests();

				sumOfNbConstraintChecks += statistics.nCcks();
				sumOfNbPropagations = statistics.nEffectiveFilterings();
				sumOfNbAssignments += statistics.nAssignments;
				sumOfNbFailedAssignments += statistics.nFailedAssignments;
				sumOfNbSolutions += statistics.solver.solManager.nSolutionsFound;

				nbPreproValuesRemoved += statistics.nPreproRemovedValues;
				nbPreproTuplesRemoved += statistics.nPreproRemovedTuples;
				nbPreproInconsistencies += statistics.nPreproInconsistencies;
				memory += Kit.getUsedMemory();

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

					map.put(Output.N_CONSTRAINT_CHECKS, (sumOfNbConstraintChecks / nbTreatedInstances));
					map.put(Output.N_EFFECTIVE_FILTERINGS, (sumOfNbPropagations / nbTreatedInstances));
					map.put(Output.N_ASSIGNMENTS, (sumOfNbAssignments / (double) nbTreatedInstances));
					map.put(Output.N_FAILED_ASSIGNMENTS, sumOfNbFailedAssignments);
					map.put(Output.N_FOUND_SOLUTIONS, (sumOfNbSolutions / (double) nbTreatedInstances));
					map.put(Output.N_REMOVED_VALUES, (nbPreproValuesRemoved / (double) nbTreatedInstances));
					map.put(Output.N_REMOVED_TUPLES, (nbPreproTuplesRemoved / (double) nbTreatedInstances));
					map.put(Output.N_FILTER_CALLS, nbFilterCallsSTR / (double) nbTreatedInstances);
					map.put(Output.AVG_TABLE_PROPORTION, sumTableProportionsSTR / nbTreatedInstances);
					map.put(Output.AVG_TABLE_SIZE, sumTableSizesSTR / nbTreatedInstances);
					map.put(Output.CPU, resolution.stopwatch.getCpuTime() / (double) nbTreatedInstances);
					map.put(Output.MEM, (long) (memory / (double) nbTreatedInstances));

					if (resolution.cp.settingExperimental.helene)
						map.put("NbRemovedValues", Kit.join(nbRemovedValues, ";"));

					if (outputElement == TypeOutput.UNSAT)
						map.put(Output.N_PREPRO_INCONSISTENCIES, nbPreproInconsistencies);

					if (resolution.cp.settingExperimental.helene) {
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

		public ActiveStatisticsMultiResolution(Resolution resolution) {
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
				else if (stats.solver.solManager.nSolutionsFound > 0)
					satStatistics[0].updateStatisticsWith(stats);
				else if (resolution.solver.isFullExploration())
					unsatStatistics[0].updateStatisticsWith(stats);
				else
					unknownStatistics[0].updateStatisticsWith(stats);
				allStatistics[0].updateStatisticsWith(stats);
				allStatistics[0].updateForMedian(stats.solvingWck, !resolution.isTimeExpiredForCurrentInstance()
						&& (stats.solver.solManager.nSolutionsFound > 0 || resolution.solver.isFullExploration()));
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
