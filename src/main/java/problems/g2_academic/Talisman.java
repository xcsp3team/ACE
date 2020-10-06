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

public class Talisman implements ProblemAPI {
	int n;
	int k;

	@Override
	public void model() {
		int limit = (n * (n * n + 1)) / 2;

		Var[][] x = array("x", size(n, n), dom(rangeClosed(1, n * n)));

		Var[][] dd = diagonalsDown(x);
		Var[][] du = diagonalsUp(x);

		allDifferent(x);
		forall(range(n), i -> sum(x[i], EQ, limit));
		forall(range(n), j -> sum(columnOf(x, j), EQ, limit));
		sum(diagonalDown(x), EQ, limit);
		sum(diagonalUp(x), EQ, limit);

		block(() -> {
			forall(range(n).range(n - 1), (i, j) -> greaterThan(dist(x[i][j], x[i][j + 1]), k));
			forall(range(n).range(n - 1), (j, i) -> greaterThan(dist(x[i][j], x[i + 1][j]), k));

			forall(range(dd.length).range(n), (i, j) -> {
				if (j < dd[i].length - 1)
					greaterThan(dist(dd[i][j], dd[i][j + 1]), k);
			});
			forall(range(du.length).range(n), (i, j) -> {
				if (j < du[i].length - 1)
					greaterThan(dist(du[i][j], du[i][j + 1]), k);
			});
		});

		// for (Var[] t : diagonalsDown(x))
		// for (int i = 0; i < t.length - 1; i++)
		// greaterThan(dist(t[i], t[i + 1]), k);
		// for (Var[] t : diagonalsUp(x))
		// for (int i = 0; i < t.length - 1; i++)
		// greaterThan(dist(t[i], t[i + 1]), k);

		// diagonalAllDown(x).forEach(t -> forall(range(t.length - 1), i -> greaterThan(dist(t[i], t[i + 1]), k)));
		// diagonalAllUp(x).forEach(t -> forall(range(t.length - 1), i -> greaterThan(dist(t[i], t[i + 1]), k)));
	}
}
