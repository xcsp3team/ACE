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

public class MarketSplit implements ProblemAPI {

	int n;
	Ctr[] ctrs;

	class Ctr {
		int[] coeffs;
		int limit;
	}

	@Override
	public void model() {
		int e = ctrs.length;

		Var[] x = array("x", size(n), dom(0, 1));

		forall(range(e), i -> sum(x, weightedBy(ctrs[i].coeffs), EQ, ctrs[i].limit)); // coeffs at 0 are automatically discarded
	}
}
// forall(range(ctrs.length), i -> sum(select(x, j -> ctrs[i].coeffs[j] != 0), select2(ctrs[i].coeffs, v -> v != 0), EQ, ctrs[i].limit));
