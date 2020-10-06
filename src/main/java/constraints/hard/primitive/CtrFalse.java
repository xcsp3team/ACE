/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.primitive;

import constraints.CtrHard;
import interfaces.FilteringSpecific;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import problem.Problem;
import variables.Variable;

public class CtrFalse extends CtrHard implements FilteringSpecific, TagFilteringCompleteAtEachCall, TagGACGuaranteed {
	@Override
	public boolean checkValues(int[] t) {
		return false;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		return false;
	}

	public CtrFalse(Problem pb, Variable[] scp) {
		super(pb, scp);
	}
}
