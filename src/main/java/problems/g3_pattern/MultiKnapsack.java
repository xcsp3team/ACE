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
import org.xcsp.modeler.api.ProblemAPI;

public class MultiKnapsack implements ProblemAPI {
	int[] objCoeffs;
	KCtr[] ctrs;

	class KCtr {
		int[] coeffs;
		int limit;
	}

	@Override
	public void model() {
		int n = objCoeffs.length, e = ctrs.length;

		Var[] x = array("x", size(n), dom(0, 1), "x[i] is 1 iff the ith item is selected");

		forall(range(e), i -> sum(x, weightedBy(ctrs[i].coeffs), LE, ctrs[i].limit));

		maximize(SUM, x, weightedBy(objCoeffs));
	}
}
