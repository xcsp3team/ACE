/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import static org.xcsp.modeler.definitions.IRootForCtrAndObj.map;

import java.util.Map;
import java.util.stream.IntStream;

import org.xcsp.modeler.definitions.ICtr.ICtrAllDifferent;

import constraints.Constraint.CtrGlobal;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import variables.Variable;

public abstract class AllDifferentAbstract extends CtrGlobal implements TagSymmetric, ICtrAllDifferent {

	@Override
	public boolean checkValues(int[] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> IntStream.range(i + 1, t.length).anyMatch(j -> t[i] == t[j]));
	}

	public AllDifferentAbstract(Problem pb, Variable[] scp) {
		super(pb, scp);
		defineKey();
	}

	@Override
	public Map<String, Object> mapXCSP() {
		return map(SCOPE, scp, LIST, compact(scp));
	}
}
