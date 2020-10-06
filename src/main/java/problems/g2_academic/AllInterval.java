/**
1 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

/**
 * Problem described at http://www.csplib.org/Problems/prob007/ <br>
 * For order 8, 9, 10, 11 and 12, there are respectively 40, 120, 296, 648 and 1328 solutions.
 * 
 */
public class AllInterval implements ProblemAPI {

	int n; // order

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(range(n)), "x[i] is the ith note of the series");

		allDifferent(x).note("notes must occur once, and so form a permutation");

		if (modelVariant("aux")) {
			Var[] y = array("y", size(n - 1), dom(range(1, n)), "y[i] is the distance between x[i] and x[i+1]");

			allDifferent(y).note("intervals between neighbouring notes must form a permutation");

			forall(range(n - 1), i -> equal(y[i], abs(sub(x[i], x[i + 1])))).note("computing distances");

			block(() -> {
				lessThan(x[0], x[n - 1]);
				lessThan(y[0], y[1]);
			}).tag(SYMMETRY_BREAKING);
		} else {
			allDifferent(treesFrom(range(n - 1), i -> abs(sub(x[i], x[i + 1])))).note("intervals between neighbouring notes must form a permutation");

			lessThan(x[0], x[n - 1]).tag(SYMMETRY_BREAKING);
		}
	}
}
