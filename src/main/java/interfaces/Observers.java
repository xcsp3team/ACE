package interfaces;

import constraints.Constraint;
import variables.Variable;

public interface Observers {

	interface ObserverConstruction {

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

	interface ObserverSearch {

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

	interface ObserverRuns {
		default void beforeRun() {
		}

		default void afterRun() {
		}
	}

	interface ObserverAssignment {

		void afterAssignment(Variable x, int a);

		void afterUnassignment(Variable x);
	}

	interface ObserverDomainReduction {
		void afterRemoval(Variable x, int a);

		void afterRemovals(Variable x, int nRemovals);
	}

	interface ObserverConflicts {

		public void whenWipeout(Constraint c, Variable x);

		// public void whenReduction(Constraint c, Variable x);
	}

	interface ObserverBacktracking {

		void restoreBefore(int depthBeforeBacktrack);

		interface ObserverBacktrackingSystematic extends ObserverBacktracking {
		}

		interface ObserverBacktrackingUnsystematic extends ObserverBacktracking {
			int lastModificationDepth();
		}
	}

}
