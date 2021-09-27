/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.intension;

import constraints.Constraint;
import interfaces.SpecificPropagator;
import problem.Problem;
import variables.Variable;

/**
 * This is the root class of any primitive constraint. A primitive constraint is a classical form of an intension
 * constraint of small arity. For example, it can be x < y, or |x-y| = z. A specific propagator is used.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Primitive extends Constraint implements SpecificPropagator {

	/**
	 * Builds a primitive constraint for the specified problem and with the specified scope
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public Primitive(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

}
