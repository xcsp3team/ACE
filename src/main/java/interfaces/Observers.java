/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package interfaces;

import constraints.Constraint;
import variables.Variable;

/**
 * These are the interfaces used for observers.
 * 
 * @author Christophe Lecoutre
 * 
 */
public interface Observers {

	/**
	 * Interface for observing the construction of the main objects: problem and solver.
	 */
	interface ObserverOnConstruction {

		/**
		 * Celled before the main objects (problem and solver) are started to be built
		 */
		default void beforeAnyConstruction() {
		}

		/**
		 * Called when the construction of the problem is finished
		 */
		default void afterProblemConstruction() {
		}

		/**
		 * Called when the construction of the solver is finished
		 */
		default void afterSolverConstruction() {
		}
	}

	/**
	 * Interface for observing the main steps of solving (preprocessing and search)
	 */
	interface ObserverOnSolving {

		/**
		 * Called before solving (preprocessing followed by search) is started
		 */
		default void beforeSolving() { // solving = prepro + search
		}

		/**
		 * Called before preprocessing is started
		 */
		default void beforePreprocessing() {
		}

		/**
		 * Called after preprocessing is finished
		 */
		default void afterPreprocessing() {
		}

		/**
		 * Called before (backtrack) search is started
		 */
		default void beforeSearch() {
		}

		/**
		 * Called after (backtrack) search is finished
		 */
		default void afterSearch() {
		}

		/**
		 * Called after solving (preprocessing followed by search) is finished
		 */
		default void afterSolving() {
		}
	}

	/**
	 * Interface for observing successive runs (possibly, only one run if restarting is deactivated) performed by the solver
	 */
	interface ObserverOnRuns {

		/**
		 * Called before the next run is started
		 */
		default void beforeRun() {
		}

		/**
		 * Called after the current run is finished
		 */
		default void afterRun() {
		}
	}

	/**
	 * Interface for observing backtracks performed by the solver
	 */
	interface ObserverOnBacktracks {

		/**
		 * Called when a restoration is required due to a backtrack coming from the specified depth
		 * 
		 * @param depthBeforeBacktrack
		 *            the depth where the backtracks started
		 */
		void restoreBefore(int depthBeforeBacktrack);

		/**
		 * Interface for observing backtracks performed by the solver. Used for observers that systematically require restoration.
		 */
		interface ObserverOnBacktracksSystematic extends ObserverOnBacktracks {
		}

		/**
		 * Interface for observing backtracks performed by the solver. Used for observers that does not systematically require restoration.
		 */
		interface ObserveronBacktracksUnsystematic extends ObserverOnBacktracks {
		}
	}

	/**
	 * Interface for observing decisions taken by the solver
	 */
	interface ObserverOnDecisions {

		/**
		 * Called when a positive decision (variable assignment x=a) is going to be taken
		 * 
		 * @param x
		 *            a variable
		 * @param a
		 *            an index (of value) for the variable x
		 */
		default void beforePositiveDecision(Variable x, int a) {
		}

		/**
		 * Called when a negative decision (value refutation x !=a) is going to be taken
		 * 
		 * @param x
		 *            a variable
		 * @param a
		 *            an index (of value) for the variable x
		 */
		default void beforeNegativeDecision(Variable x, int a) {
		}
	}

	/**
	 * Interface for observing assignments taken by the solver
	 */
	interface ObserverOnAssignments {

		/**
		 * Called after the variable assignment x=a has been taken
		 * 
		 * @param x
		 *            a variable
		 * @param a
		 *            an index (of value) for the variable x
		 */
		void afterAssignment(Variable x, int a);

		/**
		 * Called after the variable x has been unassigned (due to backtrack)
		 * 
		 * @param x
		 *            a variable
		 */
		void afterUnassignment(Variable x);
	}

	/**
	 * Interface for observing reductions of domains (typically, when filtering) by the solver
	 */
	interface ObserverOnDomainReductions {
		/**
		 * Called when the index a for the domain of x has been removed
		 * 
		 * @param x
		 *            a variable
		 * @param a
		 *            an index (of value) for the variable x
		 */
		void afterRemoval(Variable x, int a);

		/**
		 * Called when the domain of the variable x has been reduced; the number of deleted values is specified
		 * 
		 * @param x
		 *            a variable
		 * @param nRemovals
		 *            the number of deleted valued
		 */
		void afterRemovals(Variable x, int nRemovals);
	}

	/**
	 * Interface for observing conflicts encountered during search by the solver
	 */
	interface ObserverOnConflicts {

		/**
		 * Called when the domain of the specified variable has become empty (so-called domain wipeout) when filtering with the specified constraint
		 * 
		 * @param c
		 *            a constraint
		 * @param x
		 *            a variable involved in the constraint
		 */
		void whenWipeout(Constraint c, Variable x);

		// public void whenReduction(Constraint c, Variable x);
	}

}
