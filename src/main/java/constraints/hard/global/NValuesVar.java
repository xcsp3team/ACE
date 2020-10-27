/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.modeler.definitions.DefXCSP;

import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.VariableInteger;
import variables.domains.Domain;

public final class NValuesVar extends NValuesAbstract {

	protected Variable k;

	@Override
	public boolean checkValues(int[] t) {
		return IntStream.range(0, t.length - 1).map(i -> t[i]).distinct().count() == t[t.length - 1];
	}

	public NValuesVar(Problem pb, Variable[] list, VariableInteger k) {
		super(pb, pb.distinct(pb.vars(list, k)), list);
		Kit.control(Stream.of(list).noneMatch(x -> x == k), () -> "currently, k must not be present in the list");
		this.k = k;
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (x.dom.size() == 1) {
			initializeSets();
			if (k.dom.removeValuesLT(fixedVals.size()) == false || k.dom.removeValuesGT(fixedVals.size() + unfixedVars.size()) == false)
				return false;
			if (k.dom.size() == 1) {
				int limit = k.dom.uniqueValue();
				if (fixedVals.size() == limit) {
					for (int i = unfixedVars.limit; i >= 0; i--) {
						Domain dom = list[unfixedVars.dense[i]].dom;
						if (dom.removeValuesNotIn(fixedVals) == false)
							return false;
					}
				} else if (fixedVals.size() + unfixedVars.size() == limit) {
					for (int i = unfixedVars.limit; i >= 0; i--) {
						Domain dom = list[unfixedVars.dense[i]].dom;
						if (dom.removeValuesIn(fixedVals) == false)
							return false;
					}
				}
			}
		}
		return true;
	}

	@Override
	public DefXCSP defXCSP() {
		return new DefXCSP(NVALUES).addSon(LIST, compact(list)).addSon(CONDITION, "(eq," + k + ")");
	}

}
