/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.structures.forSac;

import propagation.order1.singleton.SACSharing;
import utility.exceptions.MissingImplementationException;
import variables.Variable;

/**
 * An inference manager is attached to a singleton arc consistency. <br>
 * Some such objects allow us to record domains for each pair (x,a) in order to avoid restarting the process from scratch when checking again the singleton arc
 * consistency of a value.
 */
public abstract class Inferrer {

	protected SACSharing sac;

	protected boolean enforceSPAC = false; // TODO hard coding

	public Inferrer(SACSharing sac) {
		this.sac = sac;
	}

	/**
	 * Returns an object that record the inferences (deleted values) recorded for a specified target variable when considering the assignment (x,a).
	 */
	public InferenceUnit inferenceUnit(Variable x, int a, Variable target) {
		throw new MissingImplementationException();
	}

	/**
	 * This method is called in order to remove values recorded with respect to the specified pair (x,a). It also initializes the queue.
	 * 
	 * @return false iff an inconsistency is detected
	 */
	public abstract boolean exploitInferences(Variable x, int a);

	/**
	 * This method is called in order to record values (inferred as inconsistent) with respect to the specified pair (x,a).
	 */
	public abstract void updateInferences(Variable x, int a);

	public abstract void removeInferences();
}
