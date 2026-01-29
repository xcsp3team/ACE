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

import variables.Variable;

@FunctionalInterface
/**
 * Interface for constraints implementing specific propagators
 * 
 * @author Christophe Lecoutre
 */
public interface SpecificPropagator {

	/**
	 * Runs the propagator (specific filtering algorithm) attached to the constraint implementing this interface, and returns false if an inconsistency is
	 * detected. We know that the specified variable has been picked from the propagation queue, and has been subject to a recent reduction of its domain.
	 * 
	 * @param evt
	 *            a variable whose domain has been reduced
	 * @return false if an inconsistency is detected
	 */
	boolean runPropagator(Variable evt);
}
