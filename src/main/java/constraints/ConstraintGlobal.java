/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints;

import interfaces.SpecificPropagator;
import problem.Problem;
import variables.Variable;

/**
 * The abstract class representing global constraints, which are essentially constraints with a specific form of
 * filtering (propagator).
 * 
 * @author Christophe Lecoutre
 */
public abstract class ConstraintGlobal extends Constraint implements SpecificPropagator {

	/**
	 * Builds a global constraint for the specified problem, and with the specified scope
	 * 
	 * @param pb
	 *            the problem to which this constraint belongs
	 * @param scp
	 *            the scope of the constraint
	 */
	public ConstraintGlobal(Problem pb, Variable[] scp) {
		super(pb, scp);
	}
}