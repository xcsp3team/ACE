/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import constraints.Constraint.CtrGlobal;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import variables.Domain;
import variables.Variable;

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
	public boolean runPropagator(Variable evt) {
		Variable unfixed = null;
		int uniqueFixedVal = Integer.MAX_VALUE; // this value cannot be present in integer domains
		// iteration over future variables first
		for (int i = futvars.limit; i >= 0; i--) {
			Domain dom = scp[futvars.dense[i]].dom;
			if (dom.size() > 1) {
				if (unfixed == null)
					unfixed = dom.var();
				else
					return true; // AC because at least two unfixed variables
			} else {
				if (uniqueFixedVal == Integer.MAX_VALUE)
					uniqueFixedVal = dom.uniqueValue();
				else if (uniqueFixedVal != dom.uniqueValue())
					return entailed(); // entailed because two fixed variables with different values
			}
		}
		// iteration over past variable then
		for (int i = futvars.size(); i < scp.length; i++) {
			Domain dom = scp[futvars.dense[i]].dom;
			if (uniqueFixedVal == Integer.MAX_VALUE)
				uniqueFixedVal = dom.uniqueValue();
			else if (uniqueFixedVal != dom.uniqueValue())
				return entailed();
		}
		if (unfixed == null)
			return evt.dom.fail(); // because all variables are assigned to the same value
		assert uniqueFixedVal != Integer.MAX_VALUE;
		return unfixed.dom.removeValueIfPresent(uniqueFixedVal) && entailed();
	}
}
