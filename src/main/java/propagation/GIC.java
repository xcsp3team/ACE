/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.extension.ExtensionSTR1;
import constraints.extension.ExtensionSTR3;
import heuristics.HeuristicVariables;
import heuristics.HeuristicVariablesDynamic.WdegOnDom;
import solver.Solver;
import solver.backtrack.SolverBacktrack;
import utility.Enums.EStopping;
import utility.Kit;
import utility.Kit.Stopwatch;
import variables.Domain;
import variables.Variable;

public class GIC extends StrongConsistency { // GIC is GIC1

	protected HeuristicVariables heuristic;

	public int[] nInverseTests;
	public int nITests;

	private long baseNbSolutionsLimit;

	public GIC(Solver solver) {
		super(solver);
		this.heuristic = new WdegOnDom((SolverBacktrack) solver, false);
		this.nInverseTests = new int[solver.problem.variables.length + 1];
		this.baseNbSolutionsLimit = solver.solManager.limit;
		Kit.control(solver.head.control.settingRestarts.cutoff == Long.MAX_VALUE, () -> "With GIC, there is currently no possibility of restarts.");
		Kit.control(!Stream.of(solver.problem.constraints).anyMatch(c -> c.getClass().isAssignableFrom(ExtensionSTR3.class)),
				() -> "GIC currently not compatible with STR3");

	}

	protected void handleNewSolution(Variable x, int a) {
	}

	protected boolean isInverse(Variable x, int a) {
		nInverseTests[solver.depth()]++;
		nITests++;
		solver.resetNoSolutions();
		solver.assign(x, a);
		HeuristicVariables h = ((SolverBacktrack) solver).heuristicVars;
		((SolverBacktrack) solver).heuristicVars = heuristic;
		solver.solManager.limit = 1;
		boolean inverse = enforceArcConsistencyAfterAssignment(x) && solver.doRun().stopping == EStopping.REACHED_GOAL;
		solver.solManager.limit = baseNbSolutionsLimit;
		((SolverBacktrack) solver).heuristicVars = h;
		if (inverse)
			handleNewSolution(x, a);
		else
			Kit.log.info(x + "=" + a + " is not inverse");
		solver.backtrack(x);
		return inverse;
	}

	protected void updateSTRStructures() {
		for (Constraint c : solver.problem.constraints)
			if (c instanceof ExtensionSTR1) { // || constraint instanceof AllDifferent) {
				int bef = solver.problem.nValuesRemoved;
				((ExtensionSTR1) c).runPropagator(null); // to update tables
				Kit.control(solver.problem.nValuesRemoved == bef);
			}
	}

	protected final void after(long nSolutionsBefore, int nValuesRemoved) {
		if (verbose >= 1) // && nbValuesRemoved > 0)
			Kit.log.info("nbGICInconsistentValues=" + nValuesRemoved + " at depth=" + solver.depth() + " for " + nInverseTests[solver.depth()] + " tests");
		solver.resetNoSolutions();
		solver.solManager.found = nSolutionsBefore;
		updateSTRStructures();
		performingProperSearch = false;
	}

	@Override
	public boolean enforceStrongConsistency() {
		performingProperSearch = true;
		long nSolutionsBefore = solver.solManager.found;
		int nValuesRemoved = 0;
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			Domain dom = x.dom;
			for (int a = dom.first(); a != -1; a = dom.next(a))
				if (!isInverse(x, a)) {
					x.dom.removeElementary(a);
					nValuesRemoved++;
				}
			Kit.control(dom.size() != 0, () -> "Not possible to reach inconsistency with GIC (or your instance is unsat)");
		}
		after(nSolutionsBefore, nValuesRemoved);
		return true;
	}

	/**********************************************************************************************
	 ***** Subclasses
	 *********************************************************************************************/

	public static abstract class GICAdvanced extends GIC {

		protected int[] cnts; // cnts[x] is the number of values in the current domain of x with no found support (yet)

		protected int sSupSize;
		protected int[] sSups; // nums of the variables for which GIC must be checked

		protected int cursor; // global variable used by some methods

		public GICAdvanced(Solver solver) {
			super(solver);
			this.cnts = new int[solver.problem.variables.length];
			this.sSups = new int[solver.problem.variables.length];
		}

		protected abstract void intializationAdvanced();

		protected abstract boolean isInverseAdvanced(Variable x, int a);

		@Override
		public boolean enforceStrongConsistency() {
			intializationAdvanced();
			performingProperSearch = true;
			long nSolutionsBefore = solver.solManager.found;
			int nValuesRemoved = 0;
			for (cursor = sSupSize - 1; cursor >= 0; cursor--) {
				Variable x = solver.problem.variables[sSups[cursor]];
				if (cnts[x.num] == 0)
					continue;
				Domain dom = x.dom;
				for (int a = dom.first(); a != -1; a = dom.next(a))
					if (!isInverseAdvanced(x, a)) {
						x.dom.removeElementary(a);
						nValuesRemoved++;
					}
				Kit.control(dom.size() != 0, () -> "Not possible to reach inconsistency with GIC (or your instance is unsat)");
			}
			after(nSolutionsBefore, nValuesRemoved);
			return true;
		}
	}

	public static class GIC2 extends GICAdvanced {

		protected int timestamp;

		protected int[][] stamps;

		public GIC2(Solver solver) {
			super(solver);
			this.stamps = Variable.litterals(solver.problem.variables).intArray();
		}

		protected void handleSolution(Variable x, int a, int[] solution) {
			for (int k = cursor - 1; k >= 0; k--) {
				int id = sSups[k];
				if (stamps[id][solution[id]] != timestamp) {
					stamps[id][solution[id]] = timestamp;
					cnts[id]--;
				}
			}
		}

		@Override
		protected void handleNewSolution(Variable x, int a) {
			handleSolution(x, a, solver.solManager.lastSolution);
		}

		@Override
		protected void intializationAdvanced() {
			timestamp++;
			sSupSize = 0;
			for (Variable x : solver.futVars) {
				if (x.dom.size() > 1) {
					cnts[x.num] = x.dom.size();
					sSups[sSupSize++] = x.num;
				}
			}
		}

		@Override
		protected boolean isInverseAdvanced(Variable x, int a) {
			return stamps[x.num][a] == timestamp || isInverse(x, a);
		}
	}

	public static class GIC3 extends GIC2 {

		private int[][][] residues;

		public GIC3(Solver solver) {
			super(solver);
			this.residues = Stream.of(solver.problem.variables).map(x -> new int[x.dom.initSize()][]).toArray(int[][][]::new);
		}

		protected void handleNewSolution(Variable x, int a) {
			int[] solution = solver.solManager.lastSolution;
			handleSolution(x, a, solution);
			if (residues[x.num][a] == null)
				residues[x.num][a] = new int[solver.problem.variables.length];
			Kit.copy(solution, residues[x.num][a]);
		}

		protected boolean isInverseAdvanced(Variable x, int a) {
			if (stamps[x.num][a] == timestamp)
				return true;
			if (residues[x.num][a] != null && Variable.isValidTuple(solver.problem.variables, residues[x.num][a], true)) {
				handleSolution(x, a, residues[x.num][a]);
				return true;
			}
			return isInverse(x, a);
		}
	}

	public static class GIC4 extends GICAdvanced {

		protected int[][] solutions; // recorded solutions
		private int solutionsLimit;

		protected boolean[][] gic;

		private int sValSize;
		private int[] sVal; // nums of the variables for which validity must be checked

		private int[] lastSizes;

		public GIC4(Solver solver) {
			super(solver);
			Variable[] variables = solver.problem.variables;
			solutions = new int[Variable.nInitValuesFor(variables)][];
			solutionsLimit = -1;
			gic = Variable.litterals(variables).booleanArray();
			sVal = new int[variables.length];
			lastSizes = Kit.repeat(-2, variables.length);

			algo = solver.head.control.settingExperimental.testI3;
		}

		private void handleSolution(int[] solution) {
			// Kit.control(solver.solutionManager.control(solution));
			for (int j = sSupSize - 1; j >= 0; j--) {
				int num = sSups[j];
				int a = solution[num];
				if (!gic[num][a]) {
					if (--cnts[num] == 0)
						sSups[j] = sSups[--sSupSize];
					gic[num][a] = true;
				}
			}
		}

		@Override
		protected void handleNewSolution(Variable x, int a) {
			solutionsLimit++;
			if (solutions[solutionsLimit] == null)
				solutions[solutionsLimit] = new int[solver.problem.variables.length];
			int[] solution = solver.solManager.lastSolution;
			Kit.copy(solution, solutions[solutionsLimit]);
			handleSolution(solution);
		}

		@Override
		protected void intializationAdvanced() {
			sValSize = sSupSize = 0;
			if (solver.futVars.lastPast() != null)
				sVal[sValSize++] = solver.futVars.lastPast().num;
			for (Variable x : solver.futVars) {
				int num = x.num;
				int domSize = x.dom.size();
				cnts[num] = domSize;
				if (lastSizes[num] != domSize)
					sVal[sValSize++] = num;
				sSups[sSupSize++] = num;
				Arrays.fill(gic[num], false);
			}

			Variable[] variables = solver.problem.variables;
			for (int i = solutionsLimit; i >= 0; i--) {
				int[] solution = solutions[i];
				boolean valid = true;
				for (int j = sValSize - 1; j >= 0; j--) {
					int num = sVal[j];
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
			return !performingProperSearch && !x.dom.isModifiedAtCurrentDepth() && solver.depth() != solver.head.control.settingExperimental.testI1 ? true
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
			origin = solver.head.control.settingExperimental.testI1;
			target = solver.head.control.settingExperimental.testI2;
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
					Variable[] variables = solver.problem.variables;
					allIntervals = new Interval[variables.length][];
					for (int i = 0; i < allIntervals.length; i++)
						allIntervals[i] = new Interval[variables[i].dom.initSize()];
					int nbDecisionsToReplay = origin - target - 1;
					decisionVars = new Variable[nbDecisionsToReplay];
					decisonsIdxs = new int[nbDecisionsToReplay];
					unknown = new ArrayList<>();
					inTransfer = new ArrayList<>();
					known = new List[solver.problem.variables.length + 1];
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
						for (Constraint c : solver.problem.constraints)
							if (c instanceof ExtensionSTR1) {
								int nbValuesBefore = solver.problem.nValuesRemoved;
								// int nbTuplesBefore = ((ConstraintHardExtensionSTR) constraint).getSetOfTuples().getCurrentLimit();
								((ExtensionSTR1) c).runPropagator(null);
								assert solver.problem.nValuesRemoved == nbValuesBefore;
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
			int nIntervals1 = 0;
			for (int i = 0; i < allIntervals.length; i++)
				for (int j = 0; j < allIntervals[i].length; j++)
					if (allIntervals[i][j] != null) {
						nIntervals1++;
						if (allIntervals[i][j].isFixed())
							Kit.control(known[allIntervals[i][j].maxDepth].contains(allIntervals[i][j]));
						else
							Kit.control(unknown.contains(allIntervals[i][j]));
					}
			int nIntervals2 = unknown.size();
			for (int i = target; i <= origin; i++)
				nIntervals2 += known[i].size();
			Kit.control(nIntervals1 == nIntervals2);
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

}
