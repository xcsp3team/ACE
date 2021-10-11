/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package propagation;

import static utility.Kit.control;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import heuristics.HeuristicVariables;
import heuristics.HeuristicVariables.BestScoredVariable;
import heuristics.HeuristicVariablesDynamic.WdegOnDom;
import heuristics.HeuristicVariablesDynamic.WdegVariant;
import propagation.SAC.QueueForSAC3.Cell;
import solver.Solver;
import utility.Kit;
import utility.Reflector;
import variables.Variable;

public class SAC extends StrongConsistency { // SAC is SAC1

	public int nFoundSingletons;

	/**
	 * Returns true iff (x,a) is SAC.
	 */
	protected boolean checkSAC(Variable x, int a) {
		// System.out.println("trying" + x + " " + a);
		solver.assign(x, a);
		boolean consistent = enforceArcConsistencyAfterAssignment(x);
		solver.backtrack(x);
		nSingletonTests++;
		if (!consistent)
			nEffectiveSingletonTests++;
		return consistent;
	}

	/**
	 * The method to implement for performing singleton tests on the specified variable. It returns the number of
	 * removed values.
	 */
	protected int checkSAC(Variable x) {
		int sizeBefore = x.dom.size();
		if (onlyBounds) {
			while (x.dom.size() > 0 && checkSAC(x, x.dom.first()) == false)
				x.dom.removeElementary(x.dom.first());
			while (x.dom.size() > 1 && checkSAC(x, x.dom.last()) == false)
				x.dom.removeElementary(x.dom.last());
		} else
			for (int a = x.dom.first(); a != -1; a = x.dom.next(a))
				if (checkSAC(x, a) == false)
					x.dom.removeElementary(a);
		return sizeBefore - x.dom.size();
	}

	@Override
	protected boolean enforceStrongConsistency() {
		for (int cnt = 0; cnt < nPassesLimit; cnt++) {
			long nBefore = nEffectiveSingletonTests;
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				if (onlyNeighbours && !x.isNeighborOf(solver.decisions.varOfLastDecisionIf(true)))
					continue;
				if (x.dom.size() == 1) {
					nFoundSingletons++;
					continue;
				}
				int nRemovals = checkSAC(x);
				if (nRemovals > 0 && (x.dom.size() == 0 || enforceArcConsistencyAfterRefutation(x) == false))
					return false;
				if (solver.finished())
					return true;
			}
			if (verbose > 1)
				displayPassInfo(cnt, nEffectiveSingletonTests - nBefore, nEffectiveSingletonTests - nBefore == 0);
			if (nBefore == nEffectiveSingletonTests)
				break;
		}
		assert controlAC();
		return true;
	}

	public SAC(Solver solver) {
		super(solver);
	}

	/**
	 * Control method : returns true iff (x,a) is SAC.
	 */
	private boolean controlSAC(Variable x, int a) {
		solver.assign(x, a);
		boolean consistent = enforceArcConsistencyAfterAssignment(x);
		solver.backtrack(x);
		if (!consistent)
			Kit.log.warning(x + " " + a + " not singleton consistent");
		return consistent;
	}

	/**
	 * Control method : returns true iff the CN is SAC.
	 */
	protected final boolean controlSAC() {
		if (nPassesLimit == Integer.MAX_VALUE)
			return true;
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x))
			for (int a = x.dom.first(); a != -1; a = x.dom.next(a))
				if (controlSAC(x, a) == false)
					return false;
		return true;
	}

	protected final void displayPassInfo(int cnt, long nEffective, boolean lastMessage) {
		Kit.log.info("Singleton Pass " + cnt + " nEfectiveTests=" + nEffective + " nbValuesRemoved=" + Variable.nRemovedValuesFor(solver.problem.variables)
				+ (lastMessage ? "\n" : ""));
	}

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	public static final class QueueForSAC3 {

		public final class Cell {
			public Variable x;
			public int a;

			private Cell prev, next;

			private Cell(Cell next) {
				this.next = next;
			}

			private void set(Variable x, int a, Cell prev, Cell next) {
				this.x = x;
				this.a = a;
				this.prev = prev;
				this.next = next;
			}
		}

		public interface CellSelector {
			Cell select();
		}

		public final class Fifo implements CellSelector {
			@Override
			public Cell select() {
				if (priorityToSingletons) {
					Cell cell = firstSingletonCell();
					if (cell != null)
						return cell;
				}
				for (Cell cell = head; cell != null; cell = cell.next) // first valid cell
					if (cell.x.dom.contains(cell.a))
						return cell;
				return null;
			}
		}

		public final class Lifo implements CellSelector {
			@Override
			public Cell select() {
				if (priorityToSingletons) {
					Cell cell = firstSingletonCell();
					if (cell != null)
						return cell;
				}
				for (Cell cell = tail; cell != null; cell = cell.prev) // last valid cell
					if (cell.x.dom.contains(cell.a))
						return cell;
				return null;
			}
		}

		public final class CellIterator implements CellSelector {

			private HeuristicVariables heuristic;

			public CellIterator() {
				this.heuristic = new WdegOnDom(solver, false); // hard coding
			}

			@Override
			public Cell select() {
				Cell bestCell = null;
				double bestEvaluation = -1;
				for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
					if (sizes[x.num] == 0)
						continue;
					if (priorityToSingletons && x.dom.size() == 1) {
						Cell cell = positions[x.num][x.dom.first()];
						if (cell != null)
							return cell;
					} else {
						double evaluation = heuristic == null ? sizes[x.num] : heuristic.scoreOptimizedOf(x);
						if (bestCell == null || evaluation > bestEvaluation) {
							for (int a = x.dom.first(); a != -1; a = x.dom.next(a)) {
								Cell cell = positions[x.num][a];
								if (cell != null) {
									bestCell = cell;
									bestEvaluation = evaluation;
									break;
								}
							}
						}
					}
				}
				return bestCell;
			}
		}

		private Solver solver;

		private boolean priorityToSingletons;

		private Cell head, tail, trash;
		private Cell priorityCell;

		public int size;

		private Cell[][] positions;

		private int[] sizes;

		private CellSelector cellSelector;

		public boolean isPresent(Variable x, int a) {
			return positions[x.num][a] != null;
		}

		public void setPriorityTo(Variable x, int a) {
			assert priorityCell == null && isPresent(x, a);
			priorityCell = positions[x.num][a];
		}

		public void setPriorityOf(Variable x) {
			assert priorityCell == null;
			if (sizes[x.num] == 0)
				return;
			for (int a = x.dom.first(); a != -1; a = x.dom.next(a)) {
				Cell cell = positions[x.num][a];
				if (cell != null) {
					priorityCell = cell;
					break;
				}
			}
		}

		private Cell firstSingletonCell() {
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				if (x.dom.size() == 1) {
					Cell cell = positions[x.num][x.dom.first()];
					if (cell != null)
						return cell;
				}
			}
			return null;
		}

		public Cell pickNextCell() {
			if (size == 0)
				return null;
			Cell cell = priorityCell != null ? priorityCell : cellSelector.select();
			priorityCell = null;
			if (cell != null)
				remove(cell);
			return cell; // even if removed, fields x and a are still operational (if cell is not null)
		}

		public QueueForSAC3(Solver solver, boolean priorityToSingletons) {
			this.solver = solver;
			this.priorityToSingletons = priorityToSingletons;
			this.positions = Stream.of(solver.problem.variables).map(x -> new Cell[x.dom.initSize()]).toArray(Cell[][]::new);
			IntStream.range(0, Variable.nInitValuesFor(solver.problem.variables)).forEach(i -> trash = new Cell(trash));
			this.sizes = new int[solver.problem.variables.length];
			String s = "CellIterator"; // TODO hard coding
			// settings.classForSACSelector.substring(settings.classForSACSelector.lastIndexOf('$') + 1);
			this.cellSelector = Reflector.buildObject(s, CellSelector.class, this);
		}

		public void clear() {
			size = 0;
			for (int i = 0; i < positions.length; i++)
				for (int j = 0; j < positions[i].length; j++)
					positions[i][j] = null;
			Arrays.fill(sizes, 0);
			if (head == null)
				return;
			if (trash != null) {
				tail.next = trash;
				trash.prev = tail;
			}
			trash = head;
			head = tail = null;
		}

		public void add(Variable x, int a) {
			if (positions[x.num][a] != null)
				return;
			Cell cell = trash;
			trash = trash.next;
			cell.set(x, a, tail, null);
			if (head == null)
				head = cell;
			else
				tail.next = cell;
			tail = cell;
			positions[x.num][a] = cell;
			sizes[x.num]++;
			size++;
		}

		public void remove(Cell cell) {
			Variable x = cell.x;
			int a = cell.a;
			Cell prev = cell.prev;
			Cell next = cell.next;
			if (prev == null)
				head = next;
			else
				prev.next = next;
			if (next == null)
				tail = prev;
			else
				next.prev = prev;
			cell.next = trash;
			trash = cell;
			positions[x.num][a] = null;
			sizes[x.num]--;
			size--;
		}

		public boolean remove(Variable x, int a) {
			Cell cell = positions[x.num][a];
			if (cell == null)
				return false;
			remove(cell);
			return true;
		}

		public void fill(boolean onlyBounds) {
			clear();
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				if (onlyBounds) {
					add(x, x.dom.first());
					add(x, x.dom.last());
				} else
					for (int a = x.dom.first(); a != -1; a = x.dom.next(a))
						add(x, a);
			}
		}

		public void fill() {
			fill(false);
		}

		public void display() {
			for (Cell cell = head; cell != null; cell = cell.next)
				System.out.print(cell.x + "-" + cell.a + " ");
			System.out.println();
		}
	}

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	public static abstract class SACGreedy extends SAC {

		/**
		 * Metrics for greedy SAC approaches.
		 */
		public int nBranchesBuilt, sumBranchSizes;

		/**
		 * Parameters for tuning the greedy SAC approaches.
		 */
		protected boolean maximumBranchExtension = false, stopSACWhenFoundSolution = false; // hard coding

		/**
		 * The depth at which the first singleton check of each branch is performed.
		 */
		protected int nodeDepth;

		public SACGreedy(Solver solver) {
			super(solver);
		}

		protected boolean canFindAnotherExtensionInsteadOf(Variable x, int a) {
			if (solver.depth() == nodeDepth) // meaning that branchSize = 0
				return false;
			x.dom.removeElementary(a); // to avoid considering this value again when extending the branch
			return x.dom.size() > 0 && enforceArcConsistencyAfterRefutation(x);
		}

		/**
		 * Actions to perform when a value has been detected non SAC.
		 */
		protected boolean manageInconsistentValue(Variable x, int a) {
			nEffectiveSingletonTests++;
			x.dom.removeElementary(a);
			if (shavingEvaluator != null)
				shavingEvaluator.updateRatioAfterShavingSuccess(x);
			if (x.dom.size() == 0)
				return false;
			assert queue.isEmpty();
			return enforceArcConsistencyAfterRefutation(x);
		}

		/**
		 * Restore the problem to the state it was before developing the branch.
		 */
		protected void eraseLastBuiltBranch(int branchSize) {
			nBranchesBuilt++;
			sumBranchSizes += branchSize;
			for (int i = 0; i < branchSize; i++) {
				Variable lastPast = solver.futVars.lastPast();
				solver.backtrack(lastPast);
				if (shavingEvaluator != null)
					shavingEvaluator.updateRatioAfterShavingFailure(lastPast);
			}
		}

		protected ShavingEvaluator shavingEvaluator;

		public class ShavingEvaluator { // still experimental
			private static final double INCREMENT = 0.05;

			private double ratiosThreshold;

			private double[] sucessRatios;

			private int[] nFailuresSinceLastSuccess;

			private double alpha, beta;

			public ShavingEvaluator(int nVariables, double alpha, double ratiosThreshold) {
				this.sucessRatios = new double[nVariables];
				Arrays.fill(sucessRatios, 1.0);
				this.nFailuresSinceLastSuccess = new int[nVariables];
				this.ratiosThreshold = ratiosThreshold;
				this.alpha = alpha;
				this.beta = 1 - alpha;
				assert ratiosThreshold > 0 && ratiosThreshold < 1 && alpha > 0 && alpha < 1;
			}

			public boolean isEligible(Variable x) {
				return sucessRatios[x.num] >= ratiosThreshold;
			}

			public void updateRatioAfterShavingSuccess(Variable x) {
				sucessRatios[x.num] = sucessRatios[x.num] * alpha + beta; // * SUCCESS_VALUE
				nFailuresSinceLastSuccess[x.num] = 0;
			}

			public void updateRatioAfterShavingFailure(Variable x) {
				sucessRatios[x.num] = sucessRatios[x.num] * alpha; // + beta*FAILURE_VALUE
				nFailuresSinceLastSuccess[x.num]++;
			}

			public void updateRatioAfterUntest(Variable x) {
				sucessRatios[x.num] += INCREMENT / nFailuresSinceLastSuccess[x.num];
				// sucessRatios[variable.getId()] * alpha + beta * NEUTRAL_VALUE;
			}
		}
	}

	public static class SAC3 extends SACGreedy {

		protected final QueueForSAC3 queueOfCells;

		/**
		 * 0 = desactivated ; 1 = select last failed value (when starting a new branch) ; 2 = select last failed value +
		 * last failed variable (if last branch of size 0)
		 */
		protected final int lastConflictMode;

		public SAC3(Solver solver) {
			super(solver);
			this.queueOfCells = new QueueForSAC3(solver, true);
			this.lastConflictMode = 1; // hard coding
		}

		@Override
		protected boolean manageInconsistentValue(Variable x, int a) {
			if (!super.manageInconsistentValue(x, a))
				return false;
			if (lastConflictMode == 2)
				queueOfCells.setPriorityOf(x); // for the next branch to be built
			return true;
		}

		@Override
		protected void eraseLastBuiltBranch(int branchSize) {
			if (branchSize > 0)
				super.eraseLastBuiltBranch(branchSize);
			else
				queueOfCells.clear();
			// else is possible when queue.size > 0 with elements no more valid: some indexes of the queue may have been
			// removed by AC enforcment
		}

		protected final boolean buildBranch() {
			for (Cell cell = queueOfCells.pickNextCell(); cell != null; cell = queueOfCells.pickNextCell()) {
				Variable x = cell.x;
				int a = cell.a;
				nSingletonTests++;
				if (x.dom.size() == 1)
					nFoundSingletons++;
				assert !x.assigned() && x.dom.contains(a) && queue.isEmpty();
				solver.assign(x, a);
				if (enforceArcConsistencyAfterAssignment(x)) {
					if (solver.depth() == solver.problem.variables.length) {
						System.out.println("found solution");
						if (stopSACWhenFoundSolution)
							solver.solutions.handleNewSolution();
					}
				} else {
					solver.backtrack(x);
					int lastBuiltBranchSize = solver.depth() - nodeDepth;
					if (lastBuiltBranchSize == 0)
						return manageInconsistentValue(x, a);
					queueOfCells.add(x, a);
					if (!maximumBranchExtension || !canFindAnotherExtensionInsteadOf(x, a)) {
						if (lastConflictMode > 0)
							queueOfCells.setPriorityTo(x, a); // for the next branch to be built
						break;
					}
				}
			}
			eraseLastBuiltBranch(solver.depth() - nodeDepth);
			return true;
		}

		@Override
		protected boolean enforceStrongConsistency() {
			nodeDepth = solver.depth();
			nBranchesBuilt = sumBranchSizes = 0;
			for (int cnt = 0; cnt < nPassesLimit; cnt++) {
				long nBefore = nEffectiveSingletonTests;
				queueOfCells.fill();
				while (queueOfCells.size > 0) {
					performingProperSearch = true;
					boolean consistent = buildBranch();
					performingProperSearch = false;
					if (!consistent)
						return false;
					if (stopSACWhenFoundSolution && solver.finished())
						return true; // TODO no more compatible with solver.reset()
				}
				if (verbose > 1)
					displayPassInfo(cnt, nEffectiveSingletonTests - nBefore, nEffectiveSingletonTests - nBefore == 0);
				if (nBefore == nEffectiveSingletonTests)
					break;
			}
			assert solver.finished() || (controlAC() && controlSAC());
			return true;
		}
	}

	public static class ESAC3 extends SACGreedy {

		private Variable lastFailedVar;

		private int lastFailedIdx;

		private Variable currSelectedVar;

		private int currSelectedIdx;

		private int currIndexOfVarHeuristic = -1;

		private HeuristicVariables[] varHeuristics;

		private QueueESAC queueESAC;

		class QueueESAC {

			private int nUncheckedVars;

			private Variable[] uncheckedVars;

			private BestScoredVariable bestScoredVariable = new BestScoredVariable();

			private QueueESAC() {
				this.uncheckedVars = new Variable[solver.problem.variables.length];
				control(!solver.head.control.varh.discardAux);
			}

			public void initialize() {
				nUncheckedVars = 0;
				for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x))
					if (shavingEvaluator == null || shavingEvaluator.isEligible(x))
						uncheckedVars[nUncheckedVars++] = x;
					else
						shavingEvaluator.updateRatioAfterUntest(x);
			}

			public Variable selectNextVariable() {
				bestScoredVariable.reset(false);
				if (nUncheckedVars == 0) { // we keep building the branch
					solver.futVars.execute(x -> bestScoredVariable.consider(x, varHeuristics[currIndexOfVarHeuristic].scoreOptimizedOf(x)));
				} else {
					assert controlUncheckedVariables();
					int bestPos = 0;
					for (int i = 0; i < nUncheckedVars; i++)
						if (bestScoredVariable.consider(uncheckedVars[i], varHeuristics[currIndexOfVarHeuristic].scoreOptimizedOf(uncheckedVars[i])))
							bestPos = i;
					Kit.swap(uncheckedVars, --nUncheckedVars, bestPos);
				}
				return bestScoredVariable.variable;
			}

			public Variable pick(Variable x) {
				assert uncheckedVars[nUncheckedVars
						- 1] == x : "should always be the case, because we always swap the selected variable with the one at the last position ";
				return uncheckedVars[--nUncheckedVars];
			}

			public void addLastVariable() {
				if (nUncheckedVars > 0 || uncheckedVars[0] == currSelectedVar)
					// otherwise,the last assigned variable was to keep building the branch, looking for a solution
					nUncheckedVars++;
			}

			private boolean controlUncheckedVariables() {
				IntStream.range(0, nUncheckedVars).forEach(i -> control(!uncheckedVars[i].assigned(), () -> uncheckedVars[i] + " is assigned"));
				return true;
			}
		}

		public ESAC3(Solver solver) {
			super(solver);
			this.queueESAC = new QueueESAC();
			this.varHeuristics = new HeuristicVariables[] { new WdegVariant.WdegOnDom(solver, false) };
			// including other heuristics?
			double ratio = solver.head.control.shaving.ratio, alpha = solver.head.control.shaving.alpha;
			this.shavingEvaluator = ratio != 0 ? new ShavingEvaluator(solver.problem.variables.length, alpha, ratio) : null;
		}

		private void makeSelection() {
			if (lastFailedVar == null || nBranchesBuilt < varHeuristics.length) {
				currSelectedVar = queueESAC.selectNextVariable();
				currSelectedIdx = currSelectedVar.dom.first();
			} else {
				currSelectedVar = queueESAC.pick(lastFailedVar);
				currSelectedIdx = lastFailedVar.dom.contains(lastFailedIdx) ? lastFailedIdx : lastFailedVar.dom.first();
			}
			lastFailedVar = null;
			assert !currSelectedVar.assigned() && currSelectedVar.dom.contains(currSelectedIdx) && queue.isEmpty();
		}

		protected boolean buildBranch() {
			currIndexOfVarHeuristic = (currIndexOfVarHeuristic + 1) % varHeuristics.length;
			for (boolean finished = false; !finished;) {
				makeSelection();
				nSingletonTests++;
				solver.assign(currSelectedVar, currSelectedIdx);
				if (enforceArcConsistencyAfterAssignment(currSelectedVar)) {
					if (solver.depth() == solver.problem.variables.length) {
						solver.solutions.handleNewSolution();
						finished = true;
					}
				} else {
					queueESAC.addLastVariable();
					lastFailedVar = currSelectedVar;
					lastFailedIdx = currSelectedIdx;
					solver.backtrack(currSelectedVar);
					finished = !maximumBranchExtension || !canFindAnotherExtensionInsteadOf(currSelectedVar, currSelectedIdx);
				}
			}
			int lastBuiltBranchSize = solver.depth() - nodeDepth;
			if (lastBuiltBranchSize == 0)
				return manageInconsistentValue(currSelectedVar, currSelectedIdx);
			eraseLastBuiltBranch(lastBuiltBranchSize);
			return true;
		}

		@Override
		protected boolean enforceStrongConsistency() {
			nodeDepth = solver.depth();
			nBranchesBuilt = sumBranchSizes = 0;
			lastFailedVar = null;
			queueESAC.initialize();
			long nBefore = nEffectiveSingletonTests;
			while (queueESAC.nUncheckedVars > 0) {
				performingProperSearch = true;
				boolean consistent = buildBranch();
				solver.resetNoSolutions();
				performingProperSearch = false;
				if (!consistent)
					return false;
				if (solver.finished())
					return true;
				// if (nBranchesBuilt > 1 && stopwatch.getCurrentWckTime() / 1000.0 > 40 && lastBuiltBranchSize > 0) {
				// OutputManager.printInfo("Stopping ESAC"); break; }
			}
			if (verbose > 1)
				displayPassInfo(0, nEffectiveSingletonTests - nBefore, true);
			return true;
		}
	}

}
