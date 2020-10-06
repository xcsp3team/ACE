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

// QuasiGroup-aux-v3-8.xml : 12960 solutions

public class QuasiGroup implements ProblemAPI {
	int n;

	@Override
	public void model() {
		Var[][] x = array("x", size(n, n), dom(range(n)), "x[i][j] is the value at row i and column j of the quasi-group");

		allDifferentMatrix(x).note("ensuring a Latin square");

		instantiation(diagonalDown(x), takingValues(range(n))).tag("idempotence").note("ensuring idempotence (x[i][i] = i)");

		if (modelVariant("aux-v3")) {
			Var[][] y = array("y", size(n, n), dom(range(n * n)));
			forall(range(n).range(n), (i, j) -> {
				if (i != j) {
					element(vars(x), at(y[i][j]), takingValue(i));
					intension(eq(y[i][j], add(mul(x[i][j], n), x[j][i]))); // extension for minitrack
				}
			});
		}
		if (modelVariant("aux-v4")) {
			Var[][] y = array("y", size(n, n), dom(range(n * n)));
			forall(range(n).range(n), (i, j) -> {
				if (i != j)
					element(vars(x), at(y[i][j]), takingValue(i));
			});
			forall(range(n).range(n), (i, j) -> {
				if (i != j)
					intension(eq(y[i][j], add(mul(x[j][i], n), x[i][j]))); // extension for minitrack
			});
		}
		if (modelVariant("aux-v5")) {
			Var[][] y = array("y", size(n, n), dom(range(n)));
			forall(range(n).range(n), (i, j) -> {
				if (i != j)
					element(columnOf(x, i), at(x[i][j]), takingValue(y[i][j]));
			});
			forall(range(n).range(n), (i, j) -> {
				if (i != j)
					element(columnOf(x, i), at(y[i][j]), takingValue(j));
			});
		}
		if (modelVariant("aux-v6")) {
			// problem because index is in the vector of the constraint element

			// Var[][] y = array("y", size(n, n), dom(range(n)));
			// forall(range(order).range(n), (i, j) -> {
			// if (i != j)
			// element(x[i][j], columnOf(x, j), y[i][j]);
			// });
			// forall(range(order).range(n), (i, j) -> {
			// if (i != j)
			// element(x[i][j], x[i], y[i][j]);
			// });
		}
		if (modelVariant("aux-v7")) {
			Var[][] y = array("y", size(n, n), dom(range(n)));
			forall(range(n).range(n), (i, j) -> {
				if (i != j) {
					element(columnOf(x, j), at(x[j][i]), takingValue(y[i][j]));
					element(x[i], at(x[j][i]), takingValue(y[i][j]));
				}
			});
		}

	}
}

// instantiation(select(x, (i, j) -> i == j), range(n)).note("ensuring idempotence").tag("idempotence");
