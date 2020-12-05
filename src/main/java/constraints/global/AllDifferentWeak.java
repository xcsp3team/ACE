/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.HashSet;
import java.util.Set;

import interfaces.Tags.TagGACUnguaranteed;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * This class establishes that the values assigned to the involved variables of the constraint must be all different.
 */
public final class AllDifferentWeak extends AllDifferentAbstract implements TagGACUnguaranteed { // not call filtering-complete
	private Set<Integer> set;

	private int mode = 0; // hard coding

	public AllDifferentWeak(Problem problem, Variable[] scope) {
		super(problem, scope);
		set = mode == 0 ? null : new HashSet<Integer>();
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (x.dom.size() == 1) {
			int v = x.dom.uniqueValue();
			for (int i = futvars.limit; i >= 0; i--) {
				Variable y = scp[futvars.dense[i]];
				if (y != x && y.dom.removeValueIfPresent(v) == false)
					return false;
			}
		}
		if (set == null)
			return true;
		set.clear();
		int nPastVariables = scp.length - futvars.size();
		for (int i = futvars.limit; i >= 0; i--) {
			Domain dom = scp[futvars.dense[i]].dom;
			for (int a = dom.first(); a != -1; a = dom.next(a))
				set.add(dom.toVal(a));
			if (nPastVariables + set.size() >= scp.length)
				return true;
		}
		return nPastVariables + set.size() >= scp.length;
	}

}
