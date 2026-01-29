/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package interfaces;

import java.util.List;

import constraints.Constraint;
import variables.Domain;

/**
 * An interface for objects that register constraints that are associated to them. Note that, for the moment,
 * constraints must have necessarily the same types of domains.
 * 
 * @author Christophe Lecoutre
 */
public interface ConstraintRegister {

	/**
	 * @return the list of constraints registered by this object
	 */
	abstract List<Constraint> registeredCtrs();

	/**
	 * @return the first constraint that is registered with the object
	 */
	default Constraint firstRegisteredCtr() {
		return registeredCtrs().get(0);
	}

	/**
	 * Adds a constraint to the list of constraints registered by this object
	 * 
	 * @param c
	 *            a constraint
	 */
	default void register(Constraint c) {
		assert !registeredCtrs().contains(c) && (registeredCtrs().size() == 0 || Domain.similarTypes(c.doms, firstRegisteredCtr().doms));
		registeredCtrs().add(c);
	}

	/**
	 * Removes a constraint to the list of constraints registered by this object
	 * 
	 * @param c
	 *            a constraint
	 */
	default void unregister(Constraint c) {
		boolean b = registeredCtrs().remove(c);
		assert b;
	}
}