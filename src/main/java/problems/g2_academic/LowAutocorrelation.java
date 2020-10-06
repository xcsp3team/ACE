/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class LowAutocorrelation implements ProblemAPI {
	int n;

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(-1, 1), "x[i] is the ith value of the sequence to be built.");
		Var[][] y = array("y", size(n - 1, n - 1), (k, i) -> dom(-1, 1).when(i < n - k - 1),
				"y[k][i] is the ith product value required to compute the kth auto-correlation");
		Var[] c = array("c", size(n - 1), k -> dom(range(-n + k + 1, n - k)), "c[k] is the value of the kth auto-correlation");
		// Var[] s = array("s", size(n - 1), k -> dom(range(n - k).map(v -> v * v)), "s[k] is the square of the kth auto-correlation");

		forall(range(n - 1), k -> forall(range(n - k - 1), i -> equal(y[k][i], mul(x[i], x[i + k + 1]))));
		forall(range(n - 1), k -> sum(y[k], EQ, c[k]));
		// forall(range(n - 1), k -> equal(s[k], mul(c[k], c[k])));

		minimize(SUM, treesFrom(range(n - 1), k -> mul(c[k], c[k]))).note("minimizing the sum of the squares of the auto-correlation");
	}
}
