/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.modeler.api.ProblemAPI;

public class PseudoBoolean implements ProblemAPI {

	int n, e;
	LinearCtr[] ctrs;
	LinearObj obj;

	class LinearCtr {
		int[] coeffs;
		int[] nums;
		String op;
		int limit;
	}

	class LinearObj {
		int[] coeffs;
		int[] nums;
	}

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(0, 1));

		forall(range(e), i -> {
			Var[] scp = variablesFrom(ctrs[i].nums, num -> x[num]);
			sum(scp, weightedBy(ctrs[i].coeffs), TypeConditionOperatorRel.valueFor(ctrs[i].op), ctrs[i].limit);
		}).note("respecting each linear constraint");

		if (obj != null) {
			Var[] scp = variablesFrom(obj.nums, num -> x[num]);
			minimize(SUM, scp, weightedBy(obj.coeffs)).note("minimizing the linear objective");
		}
	}
}
