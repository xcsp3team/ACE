/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import java.util.HashSet;
import java.util.Set;

import constraints.hard.CtrGlobal;
import interfaces.TagFilteringPartialAtEachCall;
import interfaces.TagGACUnguaranteed;
import problem.Problem;
import utility.sets.SetDense;
import variables.Variable;
import variables.domains.Domain;

public abstract class NValuesAbstract extends CtrGlobal implements TagGACUnguaranteed, TagFilteringPartialAtEachCall {

	protected Variable[] list;

	protected Set<Integer> fixedVals;

	protected SetDense unfixedVars;

	public NValuesAbstract(Problem pb, Variable[] scp, Variable[] list) {
		super(pb, scp);
		this.list = list;
		this.fixedVals = new HashSet<>(Variable.setOfvaluesIn(list).size());
		this.unfixedVars = new SetDense(list.length);
	}

	protected void initializeSets() {
		fixedVals.clear();
		unfixedVars.clear();
		for (int i = 0; i < list.length; i++)
			if (list[i].dom.size() == 1)
				fixedVals.add(list[i].dom.firstValue());
			else
				unfixedVars.add(i);
		boolean test = true;
		if (test) {
			for (int i = unfixedVars.limit; i >= 0; i--) {
				Domain dom = list[unfixedVars.dense[i]].dom;
				if (dom.size() > fixedVals.size())
					continue;
				if (dom.size() > 4) // hard coding for avoiding iterating systematically over all values
					continue;
				if (dom.iterateOnValuesStoppingWhen(v -> !fixedVals.contains(v)) == false)
					unfixedVars.removeAtPosition(i);
			}
		}
	}
}
