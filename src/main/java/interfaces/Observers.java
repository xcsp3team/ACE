package interfaces;

import constraints.Constraint;
import variables.Variable;

public interface Observers {

	interface ObserverOnConstruction {

		default void beforeAnyConstruction() {
		}

		/**
		 * To be called by the observer when the construction of the problem is finished.
		 */
		default void afterProblemConstruction() {
		}

		/**
		 * Method to be called by the observer when the construction of the solver is finished.
		 */
		default void afterSolverConstruction() {
		}
	}

	interface ObserverOnSearch {

		default void beforeSolving() { // solving = prepro + search
		}

		default void beforePreprocessing() {
		}

		default void afterPreprocessing() {
		}

		default void beforeSearch() {
		}

		default void afterSearch() {
		}

		default void afterSolving() {
		}
	}

	interface ObserverOnRuns {
		default void beforeRun() {
		}

		default void afterRun() {
		}
	}

	interface ObserverOnBacktracks {

		void restoreBefore(int depthBeforeBacktrack);

		interface ObserverOnBacktracksSystematic extends ObserverOnBacktracks {
		}

		interface ObserveronBacktracksUnsystematic extends ObserverOnBacktracks {
		}
	}

	interface ObserverOnDecisions {

		default void beforePositiveDecision(Variable x, int a) { // just before assignment
		}

		default void beforeNegativeDecision(Variable x, int a) { // just before refutation
		}
	}

	interface ObserverOnAssignments {

		void afterAssignment(Variable x, int a);

		void afterUnassignment(Variable x);
	}

	interface ObserverOnDomainReductions {
		void afterRemoval(Variable x, int a);

		void afterRemovals(Variable x, int nRemovals);
	}

	interface ObserverOnConflicts {

		public void whenWipeout(Constraint c, Variable x);

		// public void whenReduction(Constraint c, Variable x);
	}

}
