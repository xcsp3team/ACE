/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.order1.inverse;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.extension.ExtensionSTR1;
import search.Solver;
import utility.Kit;
import utility.Kit.Stopwatch;
import variables.Variable;
import variables.domains.Domain;

public class GIC4 extends GICAdvanced {

	protected int[][] solutions; // recorded solutions

	protected int solutionsLimit;

	protected boolean[][] gic; // 1D = variable position ; 2D = index

	private int nValVariables;

	private int[] valVariableNums; // nums of the variables for which validity must be checked

	private int[] lastSizes; // 1D = variable position ; value = last domain size

	public GIC4(Solver solver) {
		super(solver);
		Variable[] variables = solver.pb.variables;
		solutions = new int[Variable.nInitValuesFor(variables)][];
		solutionsLimit = -1;
		gic = Variable.litterals(variables).booleanArray();
		valVariableNums = new int[variables.length];
		lastSizes = Kit.repeat(-2, variables.length);

		algo = solver.rs.cp.settingExperimental.testI3;
	}

	private void handleSolution(int[] solution) {
		// Kit.control(solver.solutionManager.control(solution));
		for (int j = nSupVariables - 1; j >= 0; j--) {
			int num = supVariableNums[j];
			int a = solution[num];
			if (!gic[num][a]) {
				if (--nValuesToBeSupported[num] == 0)
					supVariableNums[j] = supVariableNums[--nSupVariables];
				gic[num][a] = true;
			}
		}
	}

	@Override
	protected void handleNewSolution(Variable x, int a) {
		solutionsLimit++;
		if (solutions[solutionsLimit] == null)
			solutions[solutionsLimit] = new int[solver.pb.variables.length];
		int[] solution = solver.solManager.lastSolution;
		Kit.copy(solution, solutions[solutionsLimit]);
		handleSolution(solution);
	}

	@Override
	protected void intializationAdvanced() {
		nValVariables = nSupVariables = 0;
		if (solver.futVars.lastPast() != null)
			valVariableNums[nValVariables++] = solver.futVars.lastPast().num;
		for (Variable x : solver.futVars) {
			int num = x.num;
			int domSize = x.dom.size();
			nValuesToBeSupported[num] = domSize;
			if (lastSizes[num] != domSize)
				valVariableNums[nValVariables++] = num;
			supVariableNums[nSupVariables++] = num;
			Arrays.fill(gic[num], false);
		}

		Variable[] variables = solver.pb.variables;
		for (int i = solutionsLimit; i >= 0; i--) {
			int[] solution = solutions[i];
			boolean valid = true;
			for (int j = nValVariables - 1; j >= 0; j--) {
				int num = valVariableNums[j];
				if (!variables[num].dom.isPresent(solution[num])) {
					valid = false;
					break;
				}
			}
			if (valid)
				handleSolution(solution);
			else {
				Kit.swap(solutions, i, solutionsLimit--);
			}
			// solution removed but we swap to save the array (in order to avoid building a new array object
		}
	}

	@Override
	protected boolean isInverseAdvanced(Variable x, int a) {
		return gic[x.num][a] || isInverse(x, a);
	}

	@Override
	public boolean enforceStrongConsistency() {
		boolean consistent = super.enforceStrongConsistency();
		restoreAfterDeletingOneDecision();
		solver.futVars.execute(x -> lastSizes[x.num] = x.dom.size());
		return consistent;
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		return !performingProperSearch && !x.dom.isModifiedAtCurrentDepth() && solver.depth() != solver.rs.cp.settingExperimental.testI1 ? true
				: super.runAfterAssignment(x);
	}

	/**********************************************************************************************
	 * Code for restoring GIC after deleting a decision
	 *********************************************************************************************/

	private int nTurns, origin, target;

	public int nVals, nUnks, nUnksAfterAC, nTests;
	public long wck, nItestsRestor;

	private Variable[] decisionVars;
	private int[] decisonsIdxs;

	private Interval[][] allIntervals; // 1D= vid ; 2D= idx

	private List<Interval> unknown;

	private List<Interval> inTransfer;

	private List<Interval>[] known; // 1D=level

	class Interval implements Comparable<Interval> {
		private Variable var;
		private int idx;
		private int minDepth;
		private int maxDepth;

		private Interval(Variable x, int a, int min, int max) {
			this.var = x;
			this.idx = a;
			this.minDepth = min;
			this.maxDepth = max;
			assert min <= max;
			if (minDepth == maxDepth)
				known[minDepth].add(this);
			else
				unknown.add(this);
		}

		private void increaseMin(int min) {
			if (this.minDepth < min) {
				this.minDepth = min;
				if (minDepth == maxDepth) {
					known[minDepth].add(this);
					inTransfer.add(this);
				}
			}
		}

		private void decreaseMax(int max) {
			if (this.maxDepth > max) {
				this.maxDepth = max;
				if (minDepth == maxDepth) {
					// System.out.println("youpi");
					known[minDepth].add(this);
					inTransfer.add(this);
				}
			}
		}

		private boolean isFixed() {
			return minDepth == maxDepth;
		}

		@Override
		public String toString() {
			return var + "=" + idx + " in [" + minDepth + ".." + maxDepth + "]";
		}

		@Override
		public int compareTo(Interval interval) {
			return Integer.compare(maxDepth, interval.maxDepth);
		}
	}

	private void buildIntervalsFor(Variable x, boolean direct) {
		int depth = solver.depth();
		boolean firstDecision = depth - 1 == target; // depth - 1 == target means that it is the decision to be removed ;
		Interval[] intervals = allIntervals[x.num];
		Domain dom = x.dom;
		for (int a = dom.lastRemoved(); a != -1 && dom.getRemovedLevelOf(a) == depth; a = dom.prevRemoved(a))
			intervals[a] = firstDecision ? new Interval(x, a, depth, origin) : new Interval(x, a, depth - 1, direct ? depth - 1 : origin);
		// origin is the largest possible value ; -1 because a decision will be removed
	}

	private void updateMaxFor(Variable x) {
		int depth = solver.depth();
		Interval[] intervals = allIntervals[x.num];
		Domain dom = x.dom;
		for (int a = dom.lastRemoved(); a != -1 && dom.getRemovedLevelOf(a) == depth; a = dom.prevRemoved(a))
			intervals[a].decreaseMax(depth);
	}

	private int finalizeIntervals() {
		int nbTests = 0;
		int nbUselessTests = 0;
		// int cnt = 0;
		while (unknown.size() > 0) {
			// cnt++;
			assert inTransfer.size() == 0;
			if (algo == 3) {
				Collections.sort(unknown);
				// System.out.println(" sorted " + unknown.size());
				int depthBefore = solver.depth();
				for (Interval interval : unknown) {
					if (inTransfer.contains(interval))
						continue;
					Kit.control(interval.minDepth <= interval.maxDepth, () -> "" + interval);
					// test x = a
					Variable x = interval.var;
					int a = interval.idx;
					int nbDecisionsTaken = solver.depth() - depthBefore, nbDecisions = interval.maxDepth - 1 - depthBefore;
					assert nbDecisions > 0;
					for (int i = nbDecisionsTaken; i < nbDecisions; i++) {
						solver.assign(decisionVars[i], decisonsIdxs[i]);
						enforceArcConsistencyAfterAssignment(decisionVars[i]);
					}
					boolean inverse = isInverse(x, a);
					nbTests++;
					if (!inverse) {
						// Kit.log.info("tests useless" + var + " " + idx + " : " + inverse);
						nbUselessTests++;
					}
					// for (int i = 0; i < nbDecisions; i++)
					// solver.backtrack();
					// update interval(s)
					if (inverse) {
						int[] solution = solutions[solutionsLimit];
						solver.futVars.execute(y -> {
							if (allIntervals[y.num][solution[y.num]] != null)
								allIntervals[y.num][solution[y.num]].increaseMin(interval.maxDepth);
						});
						solutionsLimit--;
						// mms[ind].increaseMin(mms[ind].max);
					} else
						interval.decreaseMax(interval.maxDepth - 1);
				}
				int nbDecisions = solver.depth() - depthBefore;
				for (int i = 0; i < nbDecisions; i++)
					solver.backtrack();
				Kit.control(solver.depth() == target);
			} else
				for (Interval interval : unknown) {
					if (inTransfer.contains(interval))
						continue;
					Kit.control(interval.minDepth <= interval.maxDepth, () -> "" + interval);
					// test x = a
					Variable x = interval.var;
					int a = interval.idx;
					assert solver.depth() == target;

					if (algo == 1) {
						int nbDecisions = interval.maxDepth - 1 - solver.depth();
						assert nbDecisions > 0;
						for (int i = 0; i < nbDecisions; i++) {
							solver.assign(decisionVars[i], decisonsIdxs[i]);
							enforceArcConsistencyAfterAssignment(decisionVars[i]);
						}
						boolean inverse = isInverse(x, a);
						nbTests++;
						if (!inverse) {
							// Kit.log.info("tests useless" + var + " " + idx + " : " + inverse);
							nbUselessTests++;
						}
						for (int i = 0; i < nbDecisions; i++)
							solver.backtrack();
						// update interval(s)
						if (inverse) {
							int[] solution = solutions[solutionsLimit];
							solver.futVars.execute(y -> {
								if (allIntervals[y.num][solution[y.num]] != null)
									allIntervals[y.num][solution[y.num]].increaseMin(interval.maxDepth);
							});
							solutionsLimit--;
							// mms[ind].increaseMin(mms[ind].max);
						} else
							interval.decreaseMax(interval.maxDepth - 1);
						// }
					} else {
						int nbDecisions = interval.minDepth - solver.depth();
						assert nbDecisions > 0;
						for (int i = 0; i < nbDecisions; i++) {
							solver.assign(decisionVars[i], decisonsIdxs[i]);
							enforceArcConsistencyAfterAssignment(decisionVars[i]);
						}
						boolean inverse = isInverse(x, a);
						nbTests++;
						if (inverse) {
							nbUselessTests++;
						}
						for (int i = 0; i < nbDecisions; i++)
							solver.backtrack();
						// update interval(s)
						if (inverse) {
							int[] solution = solutions[solutionsLimit];
							interval.increaseMin(interval.minDepth + 1);
							solver.futVars.execute(y -> {
								if (y != interval.var && allIntervals[y.num][solution[y.num]] != null)
									allIntervals[y.num][solution[y.num]].increaseMin(interval.minDepth);
							});
							solutionsLimit--;
							// mms[ind].increaseMin(mms[ind].max);
						} else
							interval.decreaseMax(interval.minDepth);
					}
				}
			unknown.removeAll(inTransfer);
			inTransfer.clear();
		}
		solver.resetNoSolutions();
		Kit.log.info("nbUselessTests=" + nbUselessTests);
		return nbTests;
	}

	private int algo;

	// private long cpu;

	private void restoreAfterDeletingOneDecision() {
		origin = solver.rs.cp.settingExperimental.testI1;
		target = solver.rs.cp.settingExperimental.testI2;
		if (nTurns == 0 && origin > 0 && solver.depth() == origin) {
			nTurns++;
			int nbItestsBefore = this.nITests;
			Stopwatch stopwatch = new Stopwatch();
			if (algo == 0) { // naive
				// Stopwatch stopwatch = new Stopwatch();
				int nbDecisionsToReplay = origin - target - 1;
				decisionVars = new Variable[nbDecisionsToReplay];
				decisonsIdxs = new int[nbDecisionsToReplay];

				int cnt = 0;
				while (solver.futVars.nDiscarded() > 0) {
					Variable x = solver.futVars.lastPast();
					int a = x.dom.unique();
					solver.backtrack(x);
					if (cnt == nbDecisionsToReplay)
						break;
					decisionVars[nbDecisionsToReplay - 1 - cnt] = x;
					decisonsIdxs[nbDecisionsToReplay - 1 - cnt] = a;
					cnt++;
				}
				System.out.println("Backtracked to " + solver.depth());
				for (int i = 0; i < decisionVars.length; i++) {
					solver.assign(decisionVars[i], decisonsIdxs[i]);
					// Kit.prn("new ass " + decisionVars[i] + "=" + decisonsInds[i]);
					runAfterAssignment(decisionVars[i]);
				}
			} else {
				// building structures
				Variable[] variables = solver.pb.variables;
				allIntervals = new Interval[variables.length][];
				for (int i = 0; i < allIntervals.length; i++)
					allIntervals[i] = new Interval[variables[i].dom.initSize()];
				int nbDecisionsToReplay = origin - target - 1;
				decisionVars = new Variable[nbDecisionsToReplay];
				decisonsIdxs = new int[nbDecisionsToReplay];
				unknown = new ArrayList<>();
				inTransfer = new ArrayList<>();
				known = new List[solver.pb.variables.length + 1];
				for (int i = target; i <= origin; i++)
					known[i] = new ArrayList<>();

				// initializing structures
				int cnt = 0;
				while (solver.futVars.nDiscarded() > 0) { // lastPast(); x != null; x = solver.futVars.prevPast(x)) {
					Variable x = solver.futVars.lastPast();
					int a = x.dom.unique();
					buildIntervalsFor(x, true);
					solver.futVars.execute(y -> buildIntervalsFor(y, false));
					solver.backtrack(x);
					if (cnt == nbDecisionsToReplay)
						break;
					decisionVars[nbDecisionsToReplay - 1 - cnt] = x;
					decisonsIdxs[nbDecisionsToReplay - 1 - cnt] = a;
					// Kit.prn("store " + var + " " + ind);
					cnt++;
				}
				assert controlIntervals();
				nVals = Variable.nValidValuesFor(variables);
				nUnks = unknown.size();

				// Kit.prn("after init, NbVals=" + Variable.computeNbCurrentValuesFor(variables)+ " NbUnk = " + unknown.size() + " nbDecs="
				// +
				// decisionVars.length);

				// updating intervals using AC
				performingProperSearch = true;
				for (int i = 0; i < decisionVars.length; i++) {
					solver.assign(decisionVars[i], decisonsIdxs[i]);
					// Kit.prn("new ass " + decisionVars[i] + "=" + decisonsInds[i]);
					enforceArcConsistencyAfterAssignment(decisionVars[i]);
					updateMaxFor(decisionVars[i]);
					solver.futVars.execute(y -> updateMaxFor(y));
				}
				for (int i = 0; i < decisionVars.length; i++)
					solver.backtrack();
				unknown.removeAll(inTransfer);
				inTransfer.clear();
				assert controlIntervals();

				System.out.println("After AC, NbUnk = " + unknown.size());
				// display();
				nUnksAfterAC = unknown.size();

				// finalizing intervals using inverse tests
				nTests = finalizeIntervals();
				// Kit.prn("After finalize, NbUnk = " + unknown.size() + " nbTests=" + nbTests);
				System.out.println("After Finalize");
				assert controlIntervals();

				// rebuilding the path (without the deleted decision)
				for (int i = 0; i < decisionVars.length; i++) {
					// Kit.log.info("at " + solver.getDepth() + " replay " + decisionVars[i] + "=" + decisonsIdxs[i]);
					solver.assign(decisionVars[i], decisonsIdxs[i]);
					for (Interval interval : known[solver.depth()])
						if (interval.var.dom.isPresent(interval.idx))
							interval.var.dom.removeElementary(interval.idx);
						else
							assert interval.var.dom.getRemovedLevelOf(interval.idx) == solver.depth();
					for (Constraint c : solver.pb.constraints)
						if (c instanceof ExtensionSTR1) {
							int nbValuesBefore = solver.pb.nValuesRemoved;
							// int nbTuplesBefore = ((ConstraintHardExtensionSTR) constraint).getSetOfTuples().getCurrentLimit();
							((ExtensionSTR1) c).runPropagator(null);
							assert solver.pb.nValuesRemoved == nbValuesBefore;
							// if (((ConstraintHardExtensionSTR) constraint).getSetOfTuples().getCurrentLimit() != nbTuplesBefore)
							// Kit.prn("tuples from " + constraint);
						}
				}

				Kit.log.info("nbVals=" + nVals + " nbUnks=" + nUnks + " nbUnksAfterAc=" + nUnksAfterAC + " nbTests=" + nTests);
				performingProperSearch = false;
			}
			nItestsRestor = nITests - nbItestsBefore;
			wck = stopwatch.wckTime();
			System.out.println("Wck=" + wck + " nbITestsR=" + nItestsRestor);
		}
	}

	private boolean controlIntervals() {
		Kit.control(inTransfer.size() == 0, () -> "Control cannot be performed with inTransfer not empty");
		int nbIntervals1 = 0;
		for (int i = 0; i < allIntervals.length; i++)
			for (int j = 0; j < allIntervals[i].length; j++)
				if (allIntervals[i][j] != null) {
					nbIntervals1++;
					if (allIntervals[i][j].isFixed())
						Kit.control(known[allIntervals[i][j].maxDepth].contains(allIntervals[i][j]));
					else
						Kit.control(unknown.contains(allIntervals[i][j]));
				}
		int nbIntervals2 = unknown.size();
		for (int i = target; i <= origin; i++)
			nbIntervals2 += known[i].size();
		Kit.control(nbIntervals1 == nbIntervals2);
		return true;
	}

	@SuppressWarnings("unused")
	private void display() {
		Kit.log.fine("Unknown : " + Stream.of(unknown).map(it -> it.toString()).collect(Collectors.joining(" ")));
		Kit.log.fine("Known : " + (IntStream.range(target, origin + 1)
				.mapToObj(i -> "  level " + i + " : " + (Stream.of(known[i]).map(it -> it.toString()).collect(Collectors.joining(" "))))
				.collect(Collectors.joining("\n"))));
	}

}
