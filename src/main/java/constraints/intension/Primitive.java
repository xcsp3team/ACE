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

public abstract class Primitive extends Constraint implements SpecificPropagator {

	public Primitive(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

}
