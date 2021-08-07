package propagation;

import constraints.Constraint;
import solver.Solver;
import variables.Variable;

/**
 * This class gives the description of a backward propagation technique. Such a propagation technique corresponds to a retrospective approach which works with
 * assigned variables. The domains of the unassigned variables are not modified.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Backward extends Propagation {

	public Backward(Solver solver) {
		super(solver);
	}

	@Override
	public final boolean runInitially() {
		return true; // nothing to do at preprocessing
	}

	@Override
	public final boolean runAfterRefutation(Variable x) {
		return true; // nothing to do when refuting a value
	}

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	/**
	 * The basic BT (Backtracking) algorithm.
	 */
	public static final class BT extends Backward {

		public BT(Solver solver) {
			super(solver);
		}

		@Override
		public boolean runAfterAssignment(Variable x) {
			assert x.assigned();
			for (Constraint c : x.ctrs)
				if (!c.ignored && c.futvars.size() == 0 && c.seekFirstSupport() == false)
					return false;
			return true;
		}
	}

	/**
	 * The GT (generate and test) algorithm.
	 */
	public static final class GT extends Backward {

		public GT(Solver solver) {
			super(solver);
		}

		@Override
		public boolean runAfterAssignment(Variable x) {
			assert x.assigned();
			if (solver.futVars.size() > 0)
				return true; // because we have to wait for having all variables being assigned
			for (Constraint c : solver.problem.constraints)
				if (!c.ignored && c.seekFirstSupport() == false)
					return false;
			return true;
		}
	}
}
