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

import java.util.stream.Stream;

import heuristics.HeuristicValuesDynamic.Failures;
import interfaces.Observers.ObserverOnDecisions;
import interfaces.Observers.ObserverOnRuns;
import interfaces.Observers.ObserverOnSolving;
import propagation.Forward;
import utility.Kit;
import utility.Stopwatch;
import variables.Variable;

/**
 * This class allows us to gather all statistics (as e.g., the number of backtracks) of a solver.
 * 
 * @author Christophe Lecoutre
 */
public final class Statistics implements ObserverOnSolving, ObserverOnRuns, ObserverOnDecisions {

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
		// nAssignments++; done elsewhere
	}

	@Override
	public void beforeNegativeDecision(Variable x, int a) {
		if (x.dom.size() > 1) {
			nNodes++;
			nDecisions++;
		}
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
	 * Some statistics about the assignments
	 */
	public final class Assignments {
		/**
		 * perVariable[x] is the number of assignments involving x, performed by the solver
		 */
		public final int[] perVariable;

		/**
		 * failedPerVariable[x] is is the number of failed assignments involving x, performed by the solver
		 */
		public final int[] failedPerVariable;

		/**
		 * lastFailed[x] is the last time (wrt nFailedAssignments) there was a failed assignment involving x
		 */
		public long[] lastFailed;

		/**
		 * failedPerValue[x][a] gives the number of failed assignments for (x,a)
		 */
		public int[][] failedPerValue;

		private Assignments() {
			Variable[] variables = solver.problem.variables;
			this.perVariable = Kit.repeat(2, variables.length); // initialization so as to have 0.5 as failure rate
																// initially
			this.failedPerVariable = Kit.repeat(1, variables.length);
			this.lastFailed = new long[variables.length];
			if (Stream.of(variables).anyMatch(x -> x.heuristic instanceof Failures)) {
				this.failedPerValue = new int[variables.length][];
				for (Variable x : variables)
					if (x.heuristic instanceof Failures) {
						failedPerValue[x.num] = new int[x.dom.initSize()];
						((Failures) x.heuristic).failed = failedPerValue[x.num];
					}
			}
		}

		public double failureRate(Variable x) {
			return failedPerVariable[x.num] / (double) perVariable[x.num];
		}

		public double failureAgedRate(Variable x) {
			return (failedPerVariable[x.num] / (double) perVariable[x.num]) + (1 / (double) (nFailedAssignments - lastFailed[x.num] + 1));
		}

	}

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
	 * The object used to collect data about assignments (per variable or per value)
	 */
	public final Assignments assignments;

	/**
	 * Builds an object to collect statistics about the specified solver
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public Statistics(Solver solver) {
		this.solver = solver;
		this.assignments = new Assignments();
	}

	public void whenAssignment(Variable x, int a) {
		nAssignments++;
		assignments.perVariable[x.num]++;
	}

	public void whenFailedAssignment(Variable x, int a) {
		nWrongDecisions++;
		nFailedAssignments++;
		assignments.failedPerVariable[x.num]++;
		assignments.lastFailed[x.num] = nFailedAssignments;
		if (assignments.failedPerValue != null && assignments.failedPerValue[x.num] != null)
			assignments.failedPerValue[x.num][a]++;
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