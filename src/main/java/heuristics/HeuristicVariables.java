/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package heuristics;

import static utility.Kit.control;

import java.util.Set;
import java.util.stream.Stream;

import dashboard.Control.OptionsRestarts;
import dashboard.Control.OptionsVarh;
import dashboard.Output;
import problem.Problem;
import propagation.GIC.GIC2;
import solver.Solver;
import utility.Kit;
import utility.Reflector;
import variables.DomainInfinite;
import variables.Variable;

/**
 * This is the class for building variable ordering heuristics. A variable ordering heuristic is used by a backtrack search solver to select a variable (to be
 * assigned) at each step of search.
 * 
 * @author Christophe Lecoutre
 */
public abstract class HeuristicVariables extends Heuristic {

	/**
	 * Builds and returns a variable ordering heuristic to be used with the specified solver
	 * 
	 * @param solver
	 *            the solver to which the heuristic will be attached
	 * @return a variable ordering heuristic
	 */
	public static HeuristicVariables buildFor(Solver solver) {
		Set<Class<?>> classes = solver.head.availableClasses.get(HeuristicVariables.class);
		if (solver.head.control.solving.enableSearch || solver.propagation instanceof GIC2)
			return Reflector.buildObject(solver.head.control.varh.clazz, classes, solver, solver.head.control.varh.anti);
		return null;
	}

	public static abstract class BestScored {

		protected final Solver solver;

		protected int time;

		/**
		 * true if we must prefer the variable with the lowest score, instead of the variable with the highest score
		 */
		protected boolean minimization;

		/**
		 * true if we must ignore auxiliary variables (introduced by the solver)
		 */
		private boolean discardAux;

		public BestScored(Solver solver, boolean discardAux) {
			this.solver = solver;
			this.discardAux = discardAux;
		}

		public abstract void reset();

		public BestScored beforeIteration(int time, boolean minimization) {
			this.time = time;
			this.minimization = minimization;
			return this;
		}

		protected abstract boolean considerImplem(Variable x, double s);

		/**
		 * Considers the specified variable with the specified score: compares it with the current best scored variable, and updates it if necessary.
		 * 
		 * @param x
		 *            a variable
		 * @param s
		 *            the score of the variable
		 * @return true if x becomes the new best scored variable
		 */
		public boolean consider(Variable x, double s) {
			if (discardAux && x.isAuxiliaryVariableIntroducedBySolver()) {
				assert x.id().startsWith(Problem.AUXILIARY_VARIABLE_PREFIX);
				return false;
			}
			return considerImplem(x, s);
		}

		public abstract Variable firstVariable();

		public abstract Variable secondVariable(int newTime);

	}

	/**
	 * Useful to record the best variable(s) out of a set, when considering a score computed for each of them
	 */
	public static class BestScoredSimple extends BestScored {

		/**
		 * The current best variable, i.e., the variable with the current best score; used during an iteration over all variables
		 */
		protected Variable variable;

		/**
		 * The score of the current best variable
		 */
		protected double score;

		private Variable secondVariable;

		private double secondScore;

		public BestScoredSimple(Solver solver, boolean discardAux) {
			super(solver, discardAux);
		}

		public BestScoredSimple beforeIteration(int time, boolean minimization) {
			super.beforeIteration(time, minimization);
			this.variable = null;
			this.score = minimization ? Double.MAX_VALUE : Double.NEGATIVE_INFINITY;
			this.secondVariable = null;
			return this;
		}

		public void reset() {
			this.variable = null;
			this.secondVariable = null;
		}

		public Variable second(int newTime) {
			if (secondVariable != null && this.time + 1 == newTime)
				return secondVariable;
			return null;
		}

		private boolean test = false;

		/**
		 * Considers the specified variable with the specified score: compares it with the current best scored variable, and updates it if necessary.
		 * 
		 * @param x
		 *            a variable
		 * @param s
		 *            the score of the variable
		 * @return true if x becomes the new best scored variable
		 */
		public boolean considerImplem(Variable x, double s) {
			if (test) {
				if (secondVariable != null) {
					boolean entering = ((minimization && s < secondScore) || (!minimization && s > secondScore));
					if (!entering)
						return false;
					boolean modification = ((minimization && s < score) || (!minimization && s > score));
					if (modification) {
						secondVariable = variable;
						secondScore = score;
						variable = x;
						score = s;
					} else {
						secondVariable = x;
						secondScore = s;
					}
					return false;
				} else {
					boolean modification = ((minimization && s < score) || (!minimization && s > score));
					if (modification) {
						secondVariable = variable;
						secondScore = score;
						variable = x;
						score = s;
					}
					return modification;
				}
			}
			if ((minimization && s < score) || (!minimization && s > score)) {
				secondVariable = variable;
				variable = x;
				score = s;
				return true;
			}
			return false;
		}

		public Variable firstVariable() {
			return variable;
		}

		public Variable secondVariable(int newTime) {
			if (secondVariable != null && this.time + 1 == newTime)
				return secondVariable;
			return null;
		}

		public boolean betterThan(double previousScore) {
			return minimization ? score < previousScore : score > previousScore;
		}
	}

	public static class BestScoredStacked extends BestScored {

		// private long nAssignmentsOfBranchStart = -1;
		//
		// private int depthOfBranchStart;
		//
		//
		// protected final boolean failSinceLastCall() {
		// if ((solver.stats.nAssignments - nAssignmentsOfBranchStart) != (solver.depth() - depthOfBranchStart)) {
		// nAssignmentsOfBranchStart = problem.solver.stats.nAssignments;
		// depthOfBranchStart = problem.solver.depth();
		// return true;
		// }
		// return false;
		// }

		private final int lastPossibleLimit;

		private final Variable[] vars;

		private final double[] scores;

		private int limit;

		public void reset() {
			this.limit = -1;
		}

		public BestScoredStacked(Solver solver, boolean discardAux, int capacity) {
			super(solver, discardAux);
			this.lastPossibleLimit = capacity - 1;
			this.vars = new Variable[capacity];
			this.scores = new double[capacity];
			this.limit = -1;

		}

		public BestScoredStacked beforeIteration(int time, boolean minimization) {
			super.beforeIteration(time, minimization);
			reset();
			return this;
		}

		public boolean considerImplem(Variable x, double score) {
			for (int i = 0; i <= limit; i++) {
				if (score > scores[i]) {
					for (int j = Math.min(limit, lastPossibleLimit - 1); j >= i; j--) {
						vars[j + 1] = vars[j];
						scores[j + 1] = scores[j];
					}
					vars[i] = x;
					scores[i] = score;
					if (limit < lastPossibleLimit)
						limit++;
					return i == 0;
				}
			}
			if (limit < lastPossibleLimit) {
				limit++;
				vars[limit] = x;
				scores[limit] = score;
			}
			return limit == 0;
		}

		public Variable firstVariable() {
			return limit == -1 ? null : vars[0];
		}

		public Variable secondVariable(int newTime) {
			if (limit >= 1 && this.time + 1 == newTime)
				return vars[1];
			return null;
		}

	}

	public static class BestScoredVariable3 {

		public int time;

		/**
		 * The current best variable, i.e., the variable with the current best score; used during an iteration over all variables
		 */
		public Variable variable;

		/**
		 * The score of the current best variable
		 */
		public double score;

		/**
		 * true if we must prefer the variable with the lowest score, instead of the variable with the highest score
		 */
		public boolean minimization;

		/**
		 * true if we must ignore auxiliary variables (introduced by the solver)
		 */
		private boolean discardAux;

		private Variable second;
		private double secondScore;

		public UpdateStack updateStack;

		private int stackMaxSize;

		public class UpdateStack {

			private static final int MAX = 50;

			public Variable[] cyclicVariables;

			public double[] cyclicScores;

			public int size; // modulo

			public void reset() {
				this.size = 0;
			}

			public UpdateStack() {
				this.cyclicVariables = new Variable[MAX];
				this.cyclicScores = new double[MAX];
				this.size = 0;
			}

			public void add(Variable x, double score) {
				cyclicVariables[size % MAX] = x;
				cyclicScores[size % MAX] = score;
				size++;
			}

			public Variable stackedVariableFor(int newTime) {
				int gap = newTime - time + 1; // -1 because the last variable is also recorded
				if (gap >= MAX || gap > size)
					return null;
				int idx = (size - gap + MAX) % MAX;
				return cyclicVariables[idx];
			}
		}

		public class BestStack {

			private int lastPossibleLimit;

			private Variable[] vars;

			private double[] scores;

			private int limit;

			public void reset() {
				this.limit = -1;
			}

			public BestStack(int capacity) {
				this.lastPossibleLimit = capacity - 1;
				this.vars = new Variable[capacity];
				this.scores = new double[capacity];
				this.limit = -1;
			}

			public void addPossibly(Variable x, double score) {
				for (int i = 0; i <= limit; i++) {
					if (score > scores[i]) {
						for (int j = Math.min(limit, lastPossibleLimit - 1); j >= i; j--) {
							vars[j + 1] = vars[j];
							scores[j + 1] = scores[j];
						}
						vars[i] = x;
						scores[i] = score;
						limit = Math.min(limit + 1, lastPossibleLimit);
						return;
					}
				}
				if (limit < lastPossibleLimit) {
					limit++;
					vars[limit] = x;
					scores[limit] = score;
				}
			}
		}

		public BestScoredVariable3(Solver solver, boolean discardAux, int updateStackLength) {
			this.discardAux = discardAux;
			this.stackMaxSize = updateStackLength;
			if (updateStackLength > 0)
				updateStack = new UpdateStack();
		}

		public BestScoredVariable3 beforeIteration(int time, boolean minimization) {
			this.time = time;
			this.variable = null;
			this.score = minimization ? Double.MAX_VALUE : Double.NEGATIVE_INFINITY;
			this.minimization = minimization;
			this.second = null;
			if (updateStack != null)
				updateStack.reset();
			return this;
		}

		public void cleanStack() {
			this.variable = null;
			this.second = null;
			if (updateStack != null)
				this.updateStack.reset();
		}

		public Variable second(int newTime) {
			if (second != null && this.time + 1 == newTime)
				return second;
			return null;
		}

		public Variable second2(int newTime) {
			if (updateStack == null || newTime - this.time > stackMaxSize)
				return null;

			// if (updateStack != null && this.time + 1 == newTime) {
			assert stackMaxSize != 1 || updateStack.stackedVariableFor(newTime) == second : " " + updateStack.stackedVariableFor(newTime) + " vs " + second;
			return updateStack.stackedVariableFor(newTime);
			// }
			// return null;
		}

		private boolean test = false;

		/**
		 * Considers the specified variable with the specified score: compares it with the current best scored variable, and updates it if necessary.
		 * 
		 * @param x
		 *            a variable
		 * @param s
		 *            the score of the variable
		 * @return true if x becomes the new best scored variable
		 */
		public boolean consider(Variable x, double s) {
			if (discardAux && x.isAuxiliaryVariableIntroducedBySolver()) {
				assert x.id().startsWith(Problem.AUXILIARY_VARIABLE_PREFIX);
				return false;
			}
			if (test) {
				if (second != null) {
					boolean entering = ((minimization && s < secondScore) || (!minimization && s > secondScore));
					if (!entering)
						return false;
					boolean modification = ((minimization && s < score) || (!minimization && s > score));
					if (modification) {
						second = variable;
						secondScore = score;
						variable = x;
						score = s;
						if (updateStack != null)
							updateStack.add(x, s);
					} else {
						second = x;
						secondScore = s;
					}
					return false;
				} else {
					boolean modification = ((minimization && s < score) || (!minimization && s > score));
					if (modification) {
						second = variable;
						secondScore = score;
						variable = x;
						score = s;
						if (updateStack != null)
							updateStack.add(x, s);
					}
					return modification;
				}
			}

			if ((minimization && s < score) || (!minimization && s > score)) {
				second = variable;
				variable = x;
				score = s;
				if (updateStack != null)
					updateStack.add(x, s);
				return true;
			}
			return false;
		}
	}

	/**
	 * The solver to which the heuristic is attached
	 */
	protected final Solver solver;

	/**
	 * The variables that must be assigned in priority (possibly, an empty array).
	 */
	public Variable[] priorityVars;

	/**
	 * Relevant only if priorityVars is not an array of size 0. Variables must be assigned in the order strictly given by priorityVars from 0 to
	 * nbStrictlyPriorityVars-1. Variables in priorityVars recorded between nbStriclytPriorityVars and priorityVars.length-1 must then be assigned in priority
	 * but in any order given by the heuristic. Beyond priorityVars.length-1, the heuristic can select any future variable.
	 */
	public int nStrictlyPriorityVars;

	/**
	 * The options concerning the variable ordering heuristics
	 */
	protected OptionsVarh options;

	/**
	 * The object used to record the best scored variable, when looking for it
	 */
	public BestScored bestScored;

	public final void setPriorityVars(Variable[] priorityVars, int nbStrictPriorityVars) {
		this.priorityVars = priorityVars;
		this.nStrictlyPriorityVars = nbStrictPriorityVars;
	}

	public final void resetPriorityVars() {
		this.priorityVars = new Variable[0];
		this.nStrictlyPriorityVars = 0;
	}

	public HeuristicVariables(Solver solver, boolean anti) {
		super(anti);
		this.solver = solver;
		String priority1 = solver.head.control.variables.priority1, priority2 = solver.head.control.variables.priority2;
		if (priority1.length() > 0 || priority2.length() > 0) { // used in priory wrt those of problem
			control(solver.problem.priorityArrays.length == 0 && !solver.head.control.varh.arrayPriorityRunRobin);
			Object[] p1 = Kit.extractFrom(priority1), p2 = Kit.extractFrom(priority2);
			this.priorityVars = Stream.concat(Stream.of(p1), Stream.of(p2)).map(o -> solver.problem.variableWithNumOrId(o)).toArray(Variable[]::new);
			assert Stream.of(priorityVars).distinct().count() == priorityVars.length;
			this.nStrictlyPriorityVars = p1.length;
		} else if (solver.problem.priorityArrays.length > 0) {
			control(!solver.head.control.varh.arrayPriorityRunRobin);
			if (solver.problem.priorityArrays.length == 1)
				this.priorityVars = (Variable[]) solver.problem.priorityArrays[0].flatVars;
			else
				this.priorityVars = Stream.of(solver.problem.priorityArrays).flatMap(pa -> Stream.of((Variable[]) pa.flatVars)).toArray(Variable[]::new);
			this.nStrictlyPriorityVars = 0;
		} else {
			this.priorityVars = solver.problem.priorityVars;
			this.nStrictlyPriorityVars = solver.problem.nStrictPriorityVars;
		}
		this.options = solver.head.control.varh;
		// this.bestScored = new BestScoredSimple(solver, solver.head.control.varh.discardAux); // solver.head.control.varh.updateStackLength);
		this.bestScored = new BestScoredStacked(solver, solver.head.control.varh.discardAux, 5);
	}

	/**
	 * Returns the score of the specified variable. This is the method to override when defining a new heuristic.
	 */
	public abstract double scoreOf(Variable x);

	public double scoreIfBinaryDomainOf(Variable x) {
		throw new AssertionError("Not implemented for " + this.getClass());
	}

	/**
	 * Returns the "optimized" score of the specified variable, i.e., the score of the variable while considering the optimization multiplier (to deal with
	 * either minimization or maximization).
	 * 
	 * @param x
	 *            a variable
	 * @return the "optimized" score of the specified variable
	 */
	public double scoreOptimizedOf(Variable x) {
		if (x.dom instanceof DomainInfinite) // because such variables must be computed (and not assigned); but EXPERIMENTAL
			return multiplier == -1 ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY;
		return scoreOf(x) * multiplier;
	}

	/**
	 * Returns the preferred variable among those that are priority.
	 */
	private Variable bestPriorityVariable() {
		int nPast = solver.futVars.nPast();
		if (nPast < priorityVars.length) {
			if (nPast < nStrictlyPriorityVars)
				return priorityVars[nPast];
			if (options.lc > 0) {
				Variable x = solver.lastConflict.priorityVariable();
				if (x != null && x.presentIn(priorityVars))
					return x;
			}
			Variable bestVar = null;
			double bestScore = Double.NEGATIVE_INFINITY;
			for (int i = nStrictlyPriorityVars; i < priorityVars.length; i++) {
				if (priorityVars[i].assigned())
					continue;
				double score = scoreOptimizedOf(priorityVars[i]);
				if (score > bestScore) {
					bestVar = priorityVars[i];
					bestScore = score;
				}
			}
			return bestVar;
		}
		return null;
	}

	/**
	 * Returns the preferred variable among those that are not priority.
	 */
	protected abstract Variable bestUnpriorityVariable();

	/**
	 * Returns the preferred variable, i.e., the variable that should be assigned next by the solver
	 */
	public final Variable bestVariable() {
		solver.profiler.before();
		Variable x = bestPriorityVariable();
		x = x != null ? x : bestUnpriorityVariable();
		solver.profiler.afterSelectingVariable();
		return x;
	}

	/**
	 * Returns true if the data structures of the heuristic must be reset (according to the current run)
	 * 
	 * @return true if the data structures of the heuristic must be reset
	 */
	protected boolean runReset() {
		int numRun = solver.restarter.numRun;
		OptionsRestarts options = solver.head.control.restarts;
		return ((0 < numRun && numRun % options.varhResetPeriod == 0) || (numRun - solver.solutions.last.numRun) % options.varhSolResetPeriod == 0);
	}

	public void newImpactlessAssignment(Variable x, int a) {
	}

	protected void resettingMessage(String s) {
		Kit.log.config(
				Kit.Color.YELLOW.coloring(" ...resetting ") + s + " (nValues:" + Output.numberFormat.format(Variable.nValidValuesFor(solver.problem.variables))
						+ " - nSingletons:" + Output.numberFormat.format(Variable.nSingletonsIn(solver.problem.variables)) + " - nEntailed:"
						+ Output.numberFormat.format(solver.entailed.size()) + ")");
	}

	/*************************************************************************
	 * Special heuristic
	 *************************************************************************/

	/**
	 * An implementation of COS (Conflict Ordering Search) based on ddeg/dom as underlying heuristic. IMPORTANT: new code is necessary to have COS based on
	 * wdeg/dom.
	 */
	// public static final class Memory extends HeuristicVariables implements ObserverOnRuns {
	//
	// @Override
	// public void beforeRun() {
	// nOrdered = 0;
	// }
	//
	// /**
	// * order[i] is the number of the ith variable to be assigned; valid only for i ranging from 0 to nOrdered-1.
	// */
	// private final int[] order;
	//
	// /**
	// * Indicates how many variables are currently ordered in the array order
	// */
	// private int nOrdered;
	//
	// private int posLastConflict = -1;
	//
	// public Memory(Solver solver, boolean anti) {
	// super(solver, anti);
	// this.order = new int[solver.problem.variables.length];
	// control(!options.discardAux);
	// }
	//
	// @Override
	// protected final Variable bestUnpriorityVariable() {
	// int pos = -1;
	// for (int i = 0; i < nOrdered; i++)
	// if (!solver.problem.variables[order[i]].assigned()) {
	// pos = i;
	// break;
	// }
	// if (pos != -1) {
	// if (posLastConflict > pos) {
	// control(posLastConflict < nOrdered);
	// int vid = order[pos];
	// order[pos] = order[posLastConflict];
	// order[posLastConflict] = vid;
	// }
	// posLastConflict = pos;
	// } else {
	// bestScoredVariable.reset(false);
	// solver.futVars.execute(x -> bestScoredVariable.consider(x, scoreOptimizedOf(x)));
	// pos = posLastConflict = nOrdered;
	// order[nOrdered++] = bestScoredVariable.variable.num;
	// }
	// return solver.problem.variables[order[pos]];
	// }
	//
	// @Override
	// public double scoreOf(Variable x) {
	// return x.ddeg() / (double) x.dom.size();
	// // TODO x.wdeg() is currently no more possible since weighted degrees are in another heuristic class
	// }
	// }

}