/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package heuristics;

import static utility.Kit.control;

import java.util.Set;
import java.util.stream.Stream;

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

	/**
	 * Useful to record the best variable out of a set, when considering a score computed for each of them
	 */
	public static class BestScoredVariable {

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

		public Variable second;

		public BestScoredVariable(boolean discardAux) {
			this.discardAux = discardAux;
		}

		public BestScoredVariable() {
			this(false);
		}

		public BestScoredVariable reset(boolean minimization) {
			this.variable = null;
			this.score = minimization ? Double.MAX_VALUE : Double.NEGATIVE_INFINITY;
			this.minimization = minimization;
			this.second = null;
			return this;
		}

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
			boolean modification = ((minimization && s < score) || (!minimization && s > score));
			if (modification) {
				second = variable;
				variable = x;
				score = s;
			}
			return modification;
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
	private int nStrictlyPriorityVars;

	/**
	 * The options concerning the variable ordering heuristics
	 */
	protected OptionsVarh options;

	/**
	 * The object used to record the best scored variable, when looking for it
	 */
	protected BestScoredVariable bestScoredVariable;

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
		this.bestScoredVariable = new BestScoredVariable(solver.head.control.varh.discardAux);
	}

	/**
	 * Returns the score of the specified variable. This is the method to override when defining a new heuristic.
	 */
	public abstract double scoreOf(Variable x);

	/**
	 * Returns the "optimized" score of the specified variable, i.e., the score of the variable while considering the optimization multiplier (to deal with
	 * either minimization or maximization).
	 * 
	 * @param x
	 *            a variable
	 * @return the "optimized" score of the specified variable
	 */
	public final double scoreOptimizedOf(Variable x) {
		if (x.dom instanceof DomainInfinite)
			// because such variables must be computed (and not assigned); but EXPERIMENTAL
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
		Variable x = bestPriorityVariable();
		return x != null ? x : bestUnpriorityVariable();
	}

	/**
	 * Returns true if the data structures of the heuristic must be reset (according to the current run)
	 * 
	 * @return true if the data structures of the heuristic must be reset
	 */
	protected boolean runReset() {
		int numRun = solver.restarter.numRun;
		return ((0 < numRun && numRun % solver.head.control.restarts.varhResetPeriod == 0)
				|| (numRun - solver.solutions.lastRun) % solver.head.control.restarts.varhSolResetPeriod == 0);
	}

	protected void resettingMessage(String s) {
		Kit.log.config(Kit.Color.YELLOW.coloring(" ...resetting ") + s + " (nValues: " + Output.numberFormat.format(Variable.nValidValuesFor(solver.problem.variables)) + ")");
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