package heuristics;

import solver.Solver;
import variables.Variable;

public abstract class HeuristicVariablesDirect extends HeuristicVariables {

	public HeuristicVariablesDirect(Solver solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
	}

	@Override
	public double scoreOf(Variable x) {
		throw new AssertionError("The variable must be directly selected without any iteration");
	}

	/*************************************************************************
	 * Subclasses
	 *************************************************************************/

	public static final class Rand extends HeuristicVariablesDirect {

		public Rand(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		protected Variable bestUnpriorityVar() {
			return solver.futVars.get(solver.head.random.nextInt(solver.futVars.size()));
		}
	}

}
