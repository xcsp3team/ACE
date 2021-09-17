/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package propagation;

import static utility.Kit.control;

import solver.Solver;
import utility.Enums.Branching;
import utility.Reflector;
import variables.Variable;

/**
 * This class gives the description of a forward propagation technique. Such a propagation technique corresponds to a
 * prospective approach which works with unassigned variables. The domains of the unassigned variables can be filtered.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Forward extends Propagation {

	/**
	 * The reviser object attached to the forward propagation object. <br />
	 * IMPORTANT: It is used only by constraints whose filtering algorithms are given by a generic scheme (instead of
	 * being given by specific propagators). It may be also useful when dealing with MaxCSP.
	 */
	public final Reviser reviser;

	/**
	 * Builds for the specified solver an object implementing a forward propagation technique
	 * 
	 * @param solver
	 *            the solver to which the propagation object is attached
	 */
	public Forward(Solver solver) {
		super(solver);
		this.reviser = Reflector.buildObject(settings.reviser, Reviser.class, this);
	}

	protected final boolean hasSolverPropagatedAfterLastButOneDecision() {
		return solver.head.control.solving.branching != Branching.NON || !solver.decisions.isLastButOneNegative();
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		assert x.assigned() && queue.isEmpty() : queue.size() + " " + x.assigned(); // and if PropagationIsomorphism?
		queue.add(x);
		return propagate();
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		assert !x.assigned() && queue.isEmpty() && x.dom.size() > 0;
		queue.add(x);
		return propagate();
	}

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	/**
	 * This class implements Forward Checking. This code corresponds to the <i>nFC2 </i> algorithm of: <br>
	 * "On Forward Checking for Non-binary Constraint Satisfaction", CP 1999: 88-102, by Christian Bessière, Pedro
	 * Meseguer, Eugene C. Freuder, Javier Larrosa.
	 */
	public static final class FC extends Forward {

		public FC(Solver solver) {
			super(solver);
			control(auxiliaryQueues.length == 0, () -> "For FC, we have to just use one queue");
		}

		@Override
		public boolean runInitially() {
			return true; // nothing to do
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
			return true; // nothing to do
		}
	}
}
