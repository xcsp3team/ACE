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

// 110 on CSPlib
public class PeacableArmies implements ProblemAPI {
	int n; // order

	@Override
	public void model() {
		if (modelVariant("m1")) {
			Var[][] b = array("b", size(n, n), dom(0, 1), "b[i][j] is 1 if a black queen is in the cell at row i and column j");
			Var[][] w = array("w", size(n, n), dom(0, 1), "w[i][j] is 1 if a white queen is in the cell at row i and column j");

			forall(range(n).range(n).range(n).range(n), (i1, j1, i2, j2) -> {
				if (i1 == i2 && j1 == j2)
					lessEqual(add(b[i1][j1], w[i1][j1]), 1);
				else if (i1 < i2 || (i1 == i2 && j1 < j2))
					if (i1 == i2 || j1 == j2 || Math.abs(i1 - i2) == Math.abs(j1 - j2)) {
						lessEqual(add(b[i1][j1], w[i2][j2]), 1);
						lessEqual(add(w[i1][j1], b[i2][j2]), 1);
					}
			}).note("no two opponent queens can attack each other");
			int[] coeffs = range(n * n * 2).map(i -> i < n * n ? 1 : -1);
			sum(vars(b, w), weightedBy(coeffs), EQ, 0).note("ensuring the same numbers of black and white queens");
			maximize(SUM, b).note("maximizing the number of black queens (and consequently, the size of the armies)");
		}

		if (modelVariant("m2")) {
			Var[][] x = array("x", size(n, n), dom(0, 1, 2),
					"x[i][j] is 1 (resp., 2), if a black (resp., white) queen is in the cell at row i and column j. It is 0 otherwise.");
			Var nb = var("nb", dom(range(n * n / 2)), "nb is the number of black queens");
			Var nw = var("nw", dom(range(n * n / 2)), "nw is the number of white queens");

			forall(range(n).range(n).range(n).range(n), (i1, j1, i2, j2) -> {
				if (i1 < i2 || (i1 == i2 && j1 < j2))
					if (i1 == i2 || j1 == j2 || Math.abs(i1 - i2) == Math.abs(j1 - j2))
						different(add(x[i1][j1], x[i2][j2]), 3);
			}).note("no two opponent queens can attack each other");
			count(vars(x), takingValue(1), EQ, nb).note("counting the number of black queens");
			count(vars(x), takingValue(2), EQ, nw).note("counting the number of white queens");
			equal(nb, nw).note("ensuring equal-sized armies");
			maximize(nb).note("maximizing the number of black queens (and consequently, the size of the armies)");
		}
	}
}
