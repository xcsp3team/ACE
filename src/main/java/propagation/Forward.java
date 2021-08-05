package propagation;

import solver.Solver;
import utility.Enums.EBranching;
import utility.Kit;
import utility.Reflector;
import variables.Variable;

/**
 * This class gives the description of a forward propagation technique. <br>
 * Such a propagation technique corresponds to a prospective approach which works with unassigned variables. The domains of the unassigned variables can be
 * filtered.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Forward extends Propagation {

	/**
	 * The reviser object attached to the forward propagation object.
	 */
	public Reviser reviser;

	public Forward(Solver solver) {
		super(solver);
		this.reviser = Reflector.buildObject(settings.reviser, Reviser.class, this);
	}

	protected final boolean hasSolverPropagatedAfterLastButOneDecision() {
		return solver.head.control.solving.branching != EBranching.NON || !solver.decisions.isLastButOneNegative();
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		assert x.assigned() && queue.size() == 0 : queue.size() + " " + x.assigned(); // (queue.size() == 0 || this instanceof PropagationIsomorphism)
		queue.add(x);
		return propagate();
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		assert !x.assigned() && queue.size() == 0 && x.dom.size() > 0;
		queue.add(x);
		return propagate();
	}

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	/**
	 * This class implements the <i>forward checking (mode 0) </i> technique. This mode corresponds to the <i>nFC2 </i> algorithm of: <br>
	 * [Bessiere Meseguer Freuder Larossa 99, On forward checking for non-binary constraint satisfaction].
	 */
	public static final class FC extends Forward {

		public FC(Solver solver) {
			super(solver);
			Kit.control(auxiliaryQueues.length == 0, () -> "For FC, we have to just use one queue");
		}

		@Override
		public boolean runInitially() {
			return true; // nothing to do at preprocessing
		}

		@Override
		public boolean runAfterAssignment(Variable x) {
			assert x.assigned() && queue.isEmpty();
			queue.add(x);
			boolean consistent = pickAndFilter();
			queue.clear(); // we do not consider the rest of propagation (because this is FC)
			return consistent;
		}

		@Override
		public boolean runAfterRefutation(Variable x) {
			return true; // nothing to do at refutations
		}
	}
}
