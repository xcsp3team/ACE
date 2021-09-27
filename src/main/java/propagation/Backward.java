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

import constraints.Constraint;
import solver.Solver;
import variables.Variable;

/**
 * This is the root class for backward propagation. Such form of propagation corresponds to a retrospective approach
 * that deals with assigned variables. The domains of the unassigned variables are not modified.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Backward extends Propagation {

	/**
	 * Builds a backward propagation object for the specified solver
	 * 
	 * @param solver
	 *            the solver to which the propagation object is attached
	 */
	public Backward(Solver solver) {
		super(solver);
	}

	@Override
	public final boolean runInitially() {
		return true; // nothing to do
	}

	@Override
	public final boolean runAfterRefutation(Variable x) {
		return true; // nothing to do
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
