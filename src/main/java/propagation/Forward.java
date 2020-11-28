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
}
