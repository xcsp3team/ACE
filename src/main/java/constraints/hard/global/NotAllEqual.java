/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import constraints.hard.CtrGlobal;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagSymmetric;
import problem.Problem;
import variables.Variable;
import variables.domains.Domain;

/**
 * This class establishes that the values assigned to the involved variables of the constraint must not be all equal.
 */
public class NotAllEqual extends CtrGlobal implements TagSymmetric, TagGACGuaranteed, TagFilteringCompleteAtEachCall {

	@Override
	public final boolean checkValues(int[] t) {
		for (int i = 0; i < t.length - 1; i++)
			if (t[i] != t[i + 1])
				return true;
		return false;
	}

	public NotAllEqual(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length > 2);
		defineKey();
	}

	@Override
	public int giveUpperBoundOfMaxNumberOfConflictsFor(Variable var, int idx) {
		return 1;
	}

	@Override
	public boolean runPropagator(Variable evt) {
		Variable unfixed = null;
		int uniqueFixedVal = Integer.MAX_VALUE; // this value cannot be present in integer domains
		// iteration on future variables first
		for (int i = futvars.limit; i >= 0; i--) {
			Variable y = scp[futvars.dense[i]];
			if (y.dom.size() > 1) {
				if (unfixed == null)
					unfixed = y;
				else
					return true; // AC because at least two unfixed variables
			} else {
				if (uniqueFixedVal == Integer.MAX_VALUE)
					uniqueFixedVal = y.dom.uniqueValue();
				else if (uniqueFixedVal != y.dom.uniqueValue())
					return true; // AC because two fixed variables with different values
			}
		}
		// iteration on past variable
		for (int i = futvars.size(); i < scp.length; i++) {
			Domain domp = scp[futvars.dense[i]].dom;
			if (uniqueFixedVal == Integer.MAX_VALUE)
				uniqueFixedVal = domp.uniqueValue();
			else if (uniqueFixedVal != domp.uniqueValue())
				return true;
		}
		if (unfixed == null)
			return evt.dom.fail(); // because all variables are assigned to the same value
		assert uniqueFixedVal != Integer.MAX_VALUE;
		return unfixed.dom.removeValueIfPresent(uniqueFixedVal);
	}
}
