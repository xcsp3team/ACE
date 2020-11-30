/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation;

import solver.Solver;
import solver.backtrack.SolverBacktrack;
import utility.Enums.EBranching;
import utility.Kit;
import utility.Reflector;
import variables.Variable;

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
		return solver.head.control.solving.branching != EBranching.NON || !((SolverBacktrack) solver).dr.isLastButOneDecisionNegative();
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
