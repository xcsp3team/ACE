/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.backward;

import propagation.Propagation;
import search.Solver;
import variables.Variable;

/**
 * This class gives the description of a backward propagation technique. <br>
 * Such a propagation technique corresponds to a retrospective approach which works with past variables. The domains of the future variables are not
 * modified.
 */
public abstract class PropagationBackward extends Propagation {

	public PropagationBackward(Solver solver) {
		super(solver);
	}

	@Override
	public final boolean runInitially() {
		return true; // nothing to do at preprocessing
	}

	@Override
	public final boolean runAfterRefutation(Variable x) {
		return true; // nothing to do when refuting a value
	}
}
