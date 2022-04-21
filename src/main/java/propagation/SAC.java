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

import constraints.extension.STR3;
import heuristics.HeuristicVariables;
import heuristics.HeuristicVariables.BestScoredVariable;
import heuristics.HeuristicVariablesDynamic.WdegOnDom;
import heuristics.HeuristicVariablesDynamic.WdegVariant;
import propagation.SAC.SAC3.LocalQueue.Cell;
import solver.Solver;
import utility.Kit;
import utility.Reflector;
import variables.Domain;
import variables.Variable;

/**
 * This is the class for Singleton Arc Consistency (AC). Some information about SAC and algorithms enforcing it can be
 * found for example in: <br/>
 * "Efficient algorithms for singleton arc consistency", Constraints An Int. J. 16(1): 25-53 (2011), by C. Bessiere, S.
 * Cardon, R. Debruyne, and C. Lecoutre
 * 
 * @author Christophe Lecoutre
 */
public class SAC extends StrongConsistency { // SAC is SAC1

	/**
	 * @param x
	 *            a variable
	 * @param a
	 *            a value index for x
	 * @return true iff (x,a) is SAC
	 */
	protected boolean checkSAC(Variable x, int a) {
		// System.out.println("checking" + x + " " + a);
		solver.assign(x, a);
		boolean consistent = enforceACafterAssignment(x);
		solver.backtrack(x);
		nSingletonTests++;
		if (!consistent)
			nEffectiveSingletonTests++;
		return consistent;
	}

	/**
	 * Enforces SAC on the specified variable, i.e., performs all singleton tests on the values in the domain of the
	 * specified variable
	 * 
	 * @param x
	 *            a variable
	 * @return the number of values removed by enforcing SAC on the specified variable
	 */
	protected int checkSAC(Variable x) {
		Domain dx = x.dom;
		int sizeBefore = dx.size();
		if (onlyBounds) {
			while (dx.size() > 0 && checkSAC(x, dx.first()) == false)
				dx.removeElementary(dx.first());
			while (dx.size() > 1 && checkSAC(x, dx.last()) == false)
				dx.removeElementary(dx.last());
		} else
			for (int a = dx.first(); a != -1; a = dx.next(a))
				if (checkSAC(x, a) == false)
					dx.removeElementary(a);
		return sizeBefore - dx.size();
	}

	@Override
	protected boolean enforceStrongConsistency() {
		for (int i = 0; i < nPassesLimit; i++) {
			long nBefore = nEffectiveSingletonTests;
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				if (onlyNeighbours && !x.isNeighborOf(solver.decisions.varOfLastDecisionIf(true)))
					continue;
				if (x.dom.size() == 1)
					continue;
				int nRemovals = checkSAC(x);
				if (nRemovals > 0)
					if (x.dom.size() == 0)
						return x.dom.fail();
					else if (enforceACafterRefutation(x) == false)
						return false;
				if (solver.finished())
					return true;
			}
			if (verbose > 1)
				displayPassInfo(i, nEffectiveSingletonTests - nBefore, nEffectiveSingletonTests - nBefore == 0);
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
	 * @param x
	 *            a variable
	 * @param a
	 *            a value index for x
	 * @return true iff (x,a) is SAC
	 */
	private boolean controlSAC(Variable x, int a) {
		solver.assign(x, a);
		boolean consistent = enforceACafterAssignment(x);
		solver.backtrack(x);
		if (!consistent)
			Kit.log.warning(x + " " + a + " not singleton consistent");
		return consistent;
	}

	/**
	 * 
	 * @return true iff the problem is SAC
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

	protected final void displayPassInfo(int i, long nEffective, boolean lastMessage) {
		Kit.log.info("Singleton Pass " + i + " nEfectiveTests=" + nEffective + " nbValuesRemoved=" + Variable.nRemovedValuesFor(solver.problem.variables)
				+ (lastMessage ? "\n" : ""));
	}

	/**********************************************************************************************
	 * SACGreedy, root of SAC3 and ESAC3
	 *********************************************************************************************/

	public static abstract class SACGreedy extends SAC {

		/**
		 * Metrics for greedy SAC approaches.
		 */
		public int nBranchesBuilt, sumBranchSizes;

		/**
		 * Parameters for tuning the greedy SAC approaches.
		 */
		protected boolean maximumBranchExtension = false, stopSACWhenFoundSolution = true; // hard coding

		/**
		 * The depth at which the first singleton check of each branch is performed.
		 */
		protected int nodeDepth;

		public SACGreedy(Solver solver) {
			super(solver);
		}

		protected boolean canFindAnotherExtensionInsteadOf(Variable x, int a) {
			if (solver.depth() == nodeDepth) // meaning that branch size = 0
				return false;
			x.dom.removeElementary(a); // to avoid considering this value again when extending the branch
			return x.dom.size() > 0 && enforceACafterRefutation(x);
		}

		/**
		 * Called when a literal has been shown to be SAC-inconsistent
		 * 
		 * @param x
		 *            a variable
		 * @param a
		 *            a value index for x
		 * @return false if an inconsistency is detected
		 */
		protected boolean manageInconsistentValue(Variable x, int a) {
			nEffectiveSingletonTests++;
			x.dom.removeElementary(a);
			// if (shavingEvaluator != null) shavingEvaluator.updateRatioAfterShavingSuccess(x);
			if (x.dom.size() == 0)
				return false;
			assert queue.isEmpty();
			return enforceACafterRefutation(x);
		}

		/**
		 * Restores the problem to the state it was before developing the branch
		 * 
		 * @param branchSize
		 *            the size of the branch that has just been built
		 */
		protected void eraseLastBuiltBranch(int branchSize) {
			nBranchesBuilt++;
			sumBranchSizes += branchSize;
			for (int i = 0; i < branchSize; i++) {
				Variable lastPast = solver.futVars.lastPast();
				solver.backtrack(lastPast);
				// if (shavingEvaluator != null) shavingEvaluator.updateRatioAfterShavingFailure(lastPast);
			}
		}

	}

	/**********************************************************************************************
	 * SAC3
	 *********************************************************************************************/

	/**
	 * Algorithm SAC3 for enforcing SAC in a greedy manner.
	 */
	public static class SAC3 extends SACGreedy {

		// ************************************************************************
		// ***** Inner class: LocalQueue
		// ************************************************************************

		public final class LocalQueue {

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

			public abstract class CellSelector {

				protected abstract Cell select();

				protected Cell firstSingletonCell() {
					for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x))
						if (x.dom.size() == 1) {
							Cell cell = positions[x.num][x.dom.first()];
							if (cell != null)
								return cell;
						}
					return null;
				}
			}

			public final class Fifo extends CellSelector {

				@Override
				public Cell select() {
					Cell cell = firstSingletonCell();
					if (cell != null)
						return cell;
					for (cell = head; cell != null; cell = cell.next) // first valid cell
						if (cell.x.dom.contains(cell.a))
							return cell;
					return null;
				}
			}

			public final class Lifo extends CellSelector {

				@Override
				public Cell select() {
					Cell cell = firstSingletonCell();
					if (cell != null)
						return cell;
					for (cell = tail; cell != null; cell = cell.prev) // last valid cell
						if (cell.x.dom.contains(cell.a))
							return cell;
					return null;
				}
			}

			public final class CellHeuristic extends CellSelector {

				private HeuristicVariables heuristic;

				public CellHeuristic() {
					this.heuristic = new WdegOnDom(solver, false); // hard coding
				}

				@Override
				public Cell select() {
					Cell bestCell = null;
					double bestEvaluation = -1;
					for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
						if (sizes[x.num] == 0)
							continue;
						if (x.dom.size() == 1) { // priority to singletons
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

			/**
			 * The head (first cell) of the queue
			 */
			private Cell head;

			/**
			 * The tail (last cell) of the queue
			 */
			private Cell tail;

			/**
			 * The pool of available cells
			 */
			private Cell trash;

			private Cell priorityCell;

			/**
			 * positions[x][a] indicates the cell in the queue corresponding to (x,a), or null if it is not present
			 */
			public Cell[][] positions;

			/**
			 * sizes[x] indicates the number of cells involving x in the queue
			 */
			private int[] sizes;

			/**
			 * size indicates the current number of cells in the queue
			 */
			public int size;

			/**
			 * The heuristic used to select the next cell (literal)
			 */
			private CellSelector cellSelector;

			public LocalQueue(Solver solver) {
				this.positions = Stream.of(solver.problem.variables).map(x -> new Cell[x.dom.initSize()]).toArray(Cell[][]::new);
				IntStream.range(0, Variable.nInitValuesFor(solver.problem.variables)).forEach(i -> trash = new Cell(trash));
				this.sizes = new int[solver.problem.variables.length];
				this.cellSelector = Reflector.buildObject(CellHeuristic.class.getSimpleName(), CellSelector.class, this);
				// hard coding for the choice of CellHeuristic
			}

			/**
			 * Clears the queue
			 */
			public void clear() {
				for (Cell[] t : positions)
					Arrays.fill(t, null);
				size = 0;
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

			private void fill(boolean onlyBounds) {
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

			/**
			 * Fills the queue with all possible literals
			 */
			public void fill() {
				fill(false);
			}

			/**
			 * Adds the specified literal (x,a) to the queue, if not already present
			 * 
			 * @param x
			 *            a variable
			 * @param a
			 *            a value index for x
			 */
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

			/**
			 * Removes the specified cell from the queue
			 * 
			 * @param cell
			 *            a cell
			 */
			private void remove(Cell cell) {
				size--;
				sizes[cell.x.num]--;
				positions[cell.x.num][cell.a] = null;
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
			}

			/**
			 * Picks and deletes a literal (cell) from the queue
			 * 
			 * @return the cell that has been picked and deleted, or null if there was none
			 */
			public Cell pickNextCell() {
				if (size == 0)
					return null;
				Cell cell = priorityCell != null ? priorityCell : cellSelector.select();
				priorityCell = null;
				if (cell != null)
					remove(cell);
				return cell; // even if removed, fields x and a are still operational (if cell is not null)
			}

			public void setPriorityTo(Variable x, int a) {
				assert priorityCell == null && positions[x.num][a] != null;
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

			public void display() {
				for (Cell cell = head; cell != null; cell = cell.next)
					System.out.print(cell.x + "-" + cell.a + " ");
				System.out.println();
			}
		}

		// ************************************************************************
		// ***** Class members
		// ************************************************************************

		/**
		 * The queue used for SAC3; it contains literals that must be proved to be SAC (or not)
		 */
		protected final LocalQueue localQueue;

		/**
		 * 0 = desactivated ; 1 = select last failed value (when starting a new branch) ; 2 = select last failed value +
		 * last failed variable (if last branch of size 0)
		 */
		protected final int lastConflictMode;

		public SAC3(Solver solver) {
			super(solver);
			this.localQueue = new LocalQueue(solver);
			this.lastConflictMode = 1; // hard coding
		}

		@Override
		protected boolean manageInconsistentValue(Variable x, int a) {
			if (!super.manageInconsistentValue(x, a))
				return false;
			if (lastConflictMode == 2)
				localQueue.setPriorityOf(x); // for the next branch to be built
			return true;
		}

		@Override
		protected void eraseLastBuiltBranch(int branchSize) {
			if (branchSize > 0)
				super.eraseLastBuiltBranch(branchSize);
			else
				localQueue.clear();
			// the else part is possible when queue.size > 0 with elements no more valid: some indexes of the queue may
			// have been removed by AC enforcment
		}

		private final boolean buildBranch() {
			for (Cell cell = localQueue.pickNextCell(); cell != null; cell = localQueue.pickNextCell()) {
				Variable x = cell.x;
				int a = cell.a;
				nSingletonTests++;
				assert !x.assigned() && x.dom.contains(a) && queue.isEmpty();
				solver.assign(x, a);
				if (enforceACafterAssignment(x)) {
					if (solver.depth() == solver.problem.variables.length) {
						// System.out.println("found solution");
						// if (stopSACWhenFoundSolution)
						solver.solutions.handleNewSolution();
					}
				} else {
					solver.backtrack(x);
					int lastBuiltBranchSize = solver.depth() - nodeDepth;
					if (lastBuiltBranchSize == 0)
						return manageInconsistentValue(x, a);
					localQueue.add(x, a);
					if (!maximumBranchExtension || !canFindAnotherExtensionInsteadOf(x, a)) {
						if (lastConflictMode > 0)
							localQueue.setPriorityTo(x, a); // for the next branch to be built
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
				localQueue.fill();
				while (localQueue.size > 0) {
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
			assert solver.finished() || controlAC() && controlSAC();
			return true;
		}
	}

	/**********************************************************************************************
	 * ESAC3
	 *********************************************************************************************/

	/**
	 * Algorithm ESAC3 for enforcing Existential SAC in a greedy manner.
	 */
	public static final class ESAC3 extends SACGreedy {

		// ************************************************************************
		// ***** Inner classes: ShavingEvaluator and LocalQueue
		// ************************************************************************

		private final class ShavingEvaluator { // still experimental

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

			public void updateRatioWhenIgnored(Variable x) {
				sucessRatios[x.num] += INCREMENT / nFailuresSinceLastSuccess[x.num];
				// sucessRatios[variable.getId()] * alpha + beta * NEUTRAL_VALUE;
			}
		}

		private final class LocalQueue {

			/**
			 * The number of variables that still need to be checked to be ESAC
			 */
			private int nUncheckedVars;

			/**
			 * The (dense) set of variables that still need to be checked to be ESAC
			 */
			private Variable[] uncheckedVars;

			private BestScoredVariable bestScoredVariable = new BestScoredVariable();

			private LocalQueue() {
				this.uncheckedVars = new Variable[solver.problem.variables.length];
				control(!solver.head.control.varh.discardAux);
				control(Stream.of(solver.problem.constraints).noneMatch(c -> c instanceof STR3)); // TODO why?
			}

			public void initialize() {
				nUncheckedVars = 0;
				for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x))
					if (shavingEvaluator == null || shavingEvaluator.isEligible(x))
						uncheckedVars[nUncheckedVars++] = x;
					else
						shavingEvaluator.updateRatioWhenIgnored(x);
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

			public void addLastVariable(Variable x) {
				if (nUncheckedVars > 0 || uncheckedVars[0] == x)
					// otherwise,the last assigned variable was to keep building the branch, looking for a solution
					nUncheckedVars++;
			}

			private boolean controlUncheckedVariables() {
				IntStream.range(0, nUncheckedVars).forEach(i -> control(!uncheckedVars[i].assigned(), () -> uncheckedVars[i] + " is assigned"));
				return true;
			}
		}

		// ************************************************************************
		// ***** Class members
		// ************************************************************************

		/**
		 * The queue used for ESAC3; it contains variables that must be proved to be ESAC (or not)
		 */
		private LocalQueue localQueue;

		/**
		 * The heuristics used to select variables when building branches
		 */
		private HeuristicVariables[] varHeuristics;

		/**
		 * The variable involved in the last failed singleton test
		 */
		private Variable lastFailedVar;

		/**
		 * The value index involved in the last failed singleton test
		 */
		private int lastFailedIdx;

		private int currIndexOfVarHeuristic = -1;

		protected ShavingEvaluator shavingEvaluator;

		public ESAC3(Solver solver) {
			super(solver);
			this.localQueue = new LocalQueue();
			this.varHeuristics = new HeuristicVariables[] { new WdegVariant.WdegOnDom(solver, false) };
			// including other heuristics?
			double ratio = solver.head.control.shaving.ratio, alpha = solver.head.control.shaving.alpha;
			this.shavingEvaluator = ratio != 0 ? new ShavingEvaluator(solver.problem.variables.length, alpha, ratio) : null;
		}

		private boolean buildBranch() {
			currIndexOfVarHeuristic = (currIndexOfVarHeuristic + 1) % varHeuristics.length;
			for (boolean finished = false; !finished;) {
				// making the selection
				boolean test = lastFailedVar == null || nBranchesBuilt < varHeuristics.length;
				Variable x = test ? localQueue.selectNextVariable() : localQueue.pick(lastFailedVar);
				int a = test ? x.dom.first() : x.dom.contains(lastFailedIdx) ? lastFailedIdx : x.dom.first();

				lastFailedVar = null;
				assert !x.assigned() && x.dom.contains(a) && queue.isEmpty();

				nSingletonTests++;
				solver.assign(x, a);
				if (enforceACafterAssignment(x)) {
					if (solver.depth() == solver.problem.variables.length) {
						solver.solutions.handleNewSolution();
						finished = true;
					}
				} else {
					localQueue.addLastVariable(x);
					lastFailedVar = x;
					lastFailedIdx = a;
					solver.backtrack(x);
					finished = !maximumBranchExtension || !canFindAnotherExtensionInsteadOf(x, a);
				}
				if (finished && solver.depth() == nodeDepth)
					return manageInconsistentValue(x, a);
			}
			int lastBuiltBranchSize = solver.depth() - nodeDepth;
			eraseLastBuiltBranch(lastBuiltBranchSize);
			return true;
		}

		@Override
		protected boolean enforceStrongConsistency() {
			nodeDepth = solver.depth();
			nBranchesBuilt = sumBranchSizes = 0;
			lastFailedVar = null;
			localQueue.initialize();
			long nBefore = nEffectiveSingletonTests;
			while (localQueue.nUncheckedVars > 0) {
				performingProperSearch = true;
				boolean consistent = buildBranch();
				// solver.resetNoSolutions();
				performingProperSearch = false;
				if (!consistent)
					return false;
				if (solver.finished())
					return true;
			}
			if (verbose > 1)
				displayPassInfo(0, nEffectiveSingletonTests - nBefore, true);
			return true;
		}
	}

}
