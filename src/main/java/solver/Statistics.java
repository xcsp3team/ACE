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

import interfaces.Observers.ObserverOnDecisions;
import interfaces.Observers.ObserverOnRuns;
import interfaces.Observers.ObserverOnSolving;
import propagation.Forward;
import utility.Kit.Stopwatch;
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
		prepro.nAddedNogoods = solver.nogoodRecorder != null ? solver.nogoodRecorder.nNogoods : 0;
		prepro.nAddedCtrs = solver.problem.constraints.length;
	}

	@Override
	public final void afterPreprocessing() {
		times.preproWck += stopwatch.wckTime();
		prepro.nAddedNogoods = solver.nogoodRecorder != null ? solver.nogoodRecorder.nNogoods - prepro.nAddedNogoods : 0;
		prepro.nAddedCtrs = solver.problem.constraints.length - prepro.nAddedCtrs;
		prepro.nRemovedValues = Variable.nRemovedValuesFor(solver.problem.variables);
		prepro.nRemovedTuples = solver.propagation.nTuplesRemoved;
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

	public final static class Prepro {

		public long nRemovedValues;

		public long nRemovedTuples;

		public long nAddedCtrs;

		public long nAddedNogoods;
	}

	public final class Times {

		public long solvingWck;

		public long preproWck;

		public long searchWck;

		public long firstSolWck;

		public long firstSolCpu;

		public long lastSolWck;

		public long lastSolCpu;

		/**
		 * Updates some data (times) when a new solution is found
		 */
		public void onNewSolution() {
			lastSolCpu = solver.head.stopwatch.cpuTime();
			lastSolWck = solver.head.instanceStopwatch.wckTime();
			if (solver.solutions.found == 1) {
				firstSolCpu = lastSolCpu;
				firstSolWck = lastSolWck;
			}
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
	 * The number of failed assignments (positive decisions directly leading to a failure) made by the solver when building the search tree
	 */
	public long nFailedAssignments;

	/**
	 * The object used to collect data about the preprocessing stage
	 */
	public Prepro prepro = new Prepro();

	/**
	 * The object used to collect times taken by different operations
	 */
	public Times times = new Times();

	/**
	 * Builds an object to collect statistics about the specified solver
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public Statistics(Solver solver) {
		this.solver = solver;
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