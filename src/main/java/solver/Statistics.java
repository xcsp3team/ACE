/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package solver;

import heuristics.HeuristicValuesDynamic.HeuristicUsingAssignments;
import heuristics.HeuristicValuesDynamic.HeuristicUsingAssignments.TagRequireFailedPerValue;
import heuristics.HeuristicValuesDynamic.HeuristicUsingAssignments.TagRequirePerValue;
import heuristics.HeuristicVariablesDynamic.FrOnDom;
import heuristics.HeuristicVariablesDynamic.FraOnDom;
import interfaces.Observers.ObserverOnAssignments;
import interfaces.Observers.ObserverOnDecisions;
import interfaces.Observers.ObserverOnRuns;
import interfaces.Observers.ObserverOnSolving;
import propagation.Forward;
import utility.Stopwatch;
import variables.Variable;

/**
 * This class allows us to gather all statistics (as e.g., the number of backtracks) of a solver.
 * 
 * @author Christophe Lecoutre
 */
public final class Statistics implements ObserverOnSolving, ObserverOnRuns, ObserverOnDecisions, ObserverOnAssignments {

	/*************************************************************************
	 ***** Implemented Interfaces
	 *************************************************************************/

	/**
	 * A stopwatch used to compute the time taken by some operations (e.g., construction of the problem or solver)
	 */
	private final Stopwatch stopwatch = new Stopwatch();

	@Override
	public final void beforePreprocessing() {
		stopwatch.start();
		preprocessing.nAddedNogoods = solver.nogoodReasoner != null ? solver.nogoodReasoner.nNogoods : 0;
		preprocessing.nAddedCtrs = solver.problem.constraints.length;
	}

	@Override
	public final void afterPreprocessing() {
		times.preproWck += stopwatch.wckTime();
		preprocessing.nAddedNogoods = solver.nogoodReasoner != null ? solver.nogoodReasoner.nNogoods - preprocessing.nAddedNogoods : 0;
		preprocessing.nAddedCtrs = solver.problem.constraints.length - preprocessing.nAddedCtrs;
		preprocessing.nRemovedValues = Variable.nRemovedValuesFor(solver.problem.variables);
		preprocessing.nRemovedTuples = solver.propagation.nTuplesRemoved;
	}

	@Override
	public final void beforeSolving() {
		stopwatch.start();
	}

	@Override
	public final void afterSolving() {
		times.solvingWck += stopwatch.wckTime();
	}

	@Override
	public void afterRun() {
		times.searchWck = stopwatch.wckTime();
	}

	@Override
	public void beforePositiveDecision(Variable x, int a) {
		nNodes++;
		if (x.dom.size() > 1)
			nDecisions++;
	}

	@Override
	public void beforeNegativeDecision(Variable x, int a) {
		if (x.dom.size() > 1) {
			nNodes++;
			nDecisions++;
		}
	}

	@Override
	public void afterAssignment(Variable x, int a) {
		nAssignments++;
		if (varAssignments != null && varAssignments[x.num] != null)
			varAssignments[x.num].whenAssignment(a);
	}

	@Override
	public void afterFailedAssignment(Variable x, int a) {
		nFailedAssignments++;
		if (varAssignments != null && varAssignments[x.num] != null)
			varAssignments[x.num].whenFailedAssignment(a);
		nWrongDecisions++;
	}

	@Override
	public void afterUnassignment(Variable x) {
	}

	/*************************************************************************
	 ***** Intern classes
	 *************************************************************************/

	/**
	 * Some statistics about the preprocessing phase
	 */
	public final static class Preprocessing {

		public long nRemovedValues;

		public long nRemovedTuples;

		public long nAddedCtrs;

		public long nAddedNogoods;
	}

	/**
	 * Some statistics about the times taken for some operations
	 */
	public final class Times {

		public long solvingWck;

		public long preproWck;

		public long searchWck;

		public long firstSolWck;

		public long firstSolCpu;

		public long lastSolWck;

		/**
		 * Updates some data (times) when a new solution is found
		 */
		public void onNewSolution() {
			lastSolWck = solver.head.instanceStopwatch.wckTime();
			if (solver.solutions.found == 1) {
				firstSolCpu = solver.head.stopwatch.cpuTime();
				firstSolWck = lastSolWck;
			}
		}

	}

	/**
	 * Some statistics about the assignments concerning a variable
	 */
	public final class VarAssignments {

		/**
		 * the number of assignments concerning the variable performed by the solver
		 */
		private int n;

		/**
		 * the number of failed assignments concerning the variable performed by the solver
		 */
		private int nFailed;

		/**
		 * the last time (wrt nFailedAssignments) there was a failed assignment involving the variable
		 */
		private long lastFailed;

		/**
		 * the number of assignments concerning each value of the variable
		 */
		public int[] nPerValue;

		/**
		 * the number of failed assignments concerning each value of the variable
		 */
		public int[] nFailedPerValue;

		// private int[] stack;

		private VarAssignments(Variable x, boolean buildPerValue, boolean buildFailedPerValue) {
			this.n = 2; // so as to have 0.5 as failure rate initially
			this.nFailed = 1; // so as to have 0.5 as failure rate initially
			this.nPerValue = buildPerValue ? new int[x.dom.initSize()] : null;
			this.nFailedPerValue = buildFailedPerValue ? new int[x.dom.initSize()] : null;
			if (x.heuristic instanceof HeuristicUsingAssignments)
				((HeuristicUsingAssignments) x.heuristic).assignments = this;

			// this.stack = new int[variables.length + 1];
		}

		public void whenAssignment(int a) {
			n++;
			if (nPerValue != null)
				nPerValue[a]++;
			// stack[solver.depth()] = solver.depth();
		}

		public void whenFailedAssignment(int a) {
			nFailed++;
			lastFailed = nFailedAssignments;
			if (nFailedPerValue != null)
				nFailedPerValue[a]++;
		}

		public double failureRate() {
			return nFailed / (double) n;
		}

		public double failureAgedRate() {
			return (nFailed / (double) n) + (1 / (double) (nFailedAssignments - lastFailed + 1));
		}

	}

	// /**
	// * Some statistics about the assignments
	// */
	// public final class Assignments {
	//
	// /**
	// * perVariable[x] is the number of assignments involving x, performed by the solver
	// */
	// private final int[] perVariable;
	//
	// /**
	// * failedPerVariable[x] is is the number of failed assignments involving x, performed by the solver
	// */
	// public final int[] failedPerVariable;
	//
	// /**
	// * lastFailed[x] is the last time (wrt nFailedAssignments) there was a failed assignment involving x
	// */
	// public long[] lastFailed;
	//
	// /**
	// * failedPerValue[x][a] gives the number of assignments for (x,a)
	// */
	// public int[][] perValue;
	//
	// /**
	// * failedPerValue[x][a] gives the number of failed assignments for (x,a)
	// */
	// public int[][] failedPerValue;
	//
	// // private int[] stack;
	//
	// private Assignments() {
	// Variable[] variables = solver.problem.variables;
	// this.perVariable = Kit.repeat(2, variables.length); // so as to have 0.5 as failure rate initially
	// this.failedPerVariable = Kit.repeat(1, variables.length);
	// this.lastFailed = new long[variables.length];
	//
	// for (Variable x : variables) {
	// if (x.heuristic instanceof HeuristicUsingAssignments)
	// ((HeuristicUsingAssignments) x.heuristic).assignments = this;
	//
	// }
	//
	// if (Stream.of(variables).anyMatch(x -> x.heuristic instanceof Failures)) {
	// this.failedPerValue = new int[variables.length][];
	// for (Variable x : variables)
	// if (x.heuristic instanceof Failures) {
	// failedPerValue[x.num] = new int[x.dom.initSize()];
	// ((Failures) x.heuristic).failed = failedPerValue[x.num];
	// }
	// }
	// // this.stack = new int[variables.length + 1];
	// }
	//
	// public void whenAssignment(Variable x, int a) {
	// perVariable[x.num]++;
	// // stack[solver.depth()] = solver.depth();
	// }
	//
	// public void whenFailedAssignment(Variable x, int a) {
	// failedPerVariable[x.num]++;
	// lastFailed[x.num] = nFailedAssignments;
	// if (failedPerValue != null && failedPerValue[x.num] != null)
	// failedPerValue[x.num][a]++;
	// }
	//
	// public double failureRate(Variable x) {
	// return failedPerVariable[x.num] / (double) perVariable[x.num];
	// }
	//
	// public double failureAgedRate(Variable x) {
	// return (failedPerVariable[x.num] / (double) perVariable[x.num]) + (1 / (double) (nFailedAssignments -
	// lastFailed[x.num] + 1));
	// }
	//
	// }

	/*************************************************************************
	 ***** Fields and Methods
	 *************************************************************************/

	/**
	 * The solver to which this object is attached
	 */
	public final Solver solver;

	/**
	 * The number of nodes of the search tree built by the solver
	 */
	public long nNodes = 1;

	/**
	 * The number of decisions taken by the solver when building the search tree
	 */
	public long nDecisions;

	/**
	 * The number of wrong decisions taken by the solver when building the search tree
	 */
	public long nWrongDecisions;

	/**
	 * The number of backtracks in the search tree built by the solver
	 */
	public long nBacktracks;

	/**
	 * The number of assignments (positive decisions) made by the solver when building the search tree
	 */
	public long nAssignments;

	/**
	 * The number of failed assignments (positive decisions directly leading to a failure) made by the solver when
	 * building the search tree
	 */
	public long nFailedAssignments;

	/**
	 * The object used to collect data about the preprocessing stage
	 */
	public final Preprocessing preprocessing = new Preprocessing();

	/**
	 * The object used to collect times taken by different operations
	 */
	public final Times times = new Times();

	/**
	 * The array of objects used to collect data about assignments (per variable or per value)
	 */
	public VarAssignments[] varAssignments;

	/**
	 * Builds an object to collect statistics about the specified solver
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public Statistics(Solver solver) {
		this.solver = solver;
		Variable[] vars = solver.problem.variables;
		boolean b1 = solver.heuristic instanceof FrOnDom || solver.heuristic instanceof FraOnDom;
		if (b1)
			varAssignments = new VarAssignments[vars.length];
		for (int i = 0; i < vars.length; i++) {
			boolean b2 = vars[i].heuristic instanceof TagRequirePerValue;
			boolean b3 = vars[i].heuristic instanceof TagRequireFailedPerValue;
			if (b1 || b2 || b3) {
				if (varAssignments == null)
					varAssignments = new VarAssignments[vars.length];
				varAssignments[i] = new VarAssignments(vars[i], b2, b3);
			}
		}
	}

	public long safeNumber() {
		return nNodes + nAssignments + nBacktracks;
	}

	public final long nRevisions() {
		return solver.propagation instanceof Forward ? ((Forward) solver.propagation).reviser.nRevisions : 0;
	}

	public final long nUselessRevisions() {
		return solver.propagation instanceof Forward ? ((Forward) solver.propagation).reviser.nUselessRevisions : 0;
	}

}