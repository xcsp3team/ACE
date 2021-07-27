/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics;

import interfaces.Tags.TagMaximize;

public abstract class Heuristic {

	/**
	 * The coefficient used when computing scores of objects, the one with the best score being selected by this heuristic. The best one is the smallest one if
	 * the coefficient is -1 (minimization) and it is the greatest one if the coefficient is +1 (maximization).
	 */
	public int scoreCoeff;

	public Heuristic(boolean antiHeuristic) {
		// we translate the specified constant into a coefficient that can be used directly when computing scores
		this.scoreCoeff = (!antiHeuristic && !(this instanceof TagMaximize)) || (antiHeuristic && this instanceof TagMaximize) ? -1 : 1;
	}

	public void reset() {
	}
}