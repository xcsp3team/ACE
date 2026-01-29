/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package heuristics;

import interfaces.Tags.TagMaximize;

/**
 * This is the abstract root class used for representing any kind of heuristics (variable ordering heuristics, value
 * ordering heuristics, revision ordering heuristics, etc.).
 * 
 * @author Christophe Lecoutre
 *
 */
public abstract class Heuristic {

	/**
	 * The coefficient used when computing scores of objects, the one with the best score being selected by the
	 * heuristic. The best one is the smallest one if the multiplier/coefficient is -1 (minimization) and it is the
	 * greatest one if the multiplier is +1 (maximization).
	 */
	public int multiplier;

	/**
	 * Builds an heuristic
	 * 
	 * @param anti
	 *            indicates if one must take the reverse ordering of the natural one
	 */
	public Heuristic(boolean anti) {
		// we translate the specified Boolean into a coefficient that can be used directly when computing scores
		this.multiplier = (!anti && !(this instanceof TagMaximize)) || (anti && this instanceof TagMaximize) ? -1 : 1;
	}

	/**
	 * Resets some structures associated with the heuristic
	 */
	public void reset() {
	}
}