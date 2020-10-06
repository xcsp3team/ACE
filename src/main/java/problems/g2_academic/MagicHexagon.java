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
import org.xcsp.common.Range;
import org.xcsp.modeler.api.ProblemAPI;

//java abscon.Resolution problems.acad.MagicHexagon 5 6 => 1 sol in 50s
public class MagicHexagon implements ProblemAPI {
	int n; // order
	int s; // start

	private Var[] scopeForDiagonal(Var[][] x, int i, boolean right) {
		int d = x.length;
		int v1 = right ? Math.max(0, d / 2 - i) : Math.max(0, i - d / 2), v2 = d / 2 - v1;
		Range r = range(d - Math.abs(d / 2 - i));
		return variablesFrom(r, j -> x[j + v1][i - Math.max(0, right ? v2 - j : j - v2)]);
	}

	@Override
	public void model() {
		int gap = 3 * n * n - 3 * n + 1;
		int sum = sumOf(range(s, s + gap));
		control(sum % (2 * n - 1) == 0, "No magic hexagon for order=" + n + " and start=" + s);
		int magic = sum / (2 * n - 1);
		int d = n + n - 1; // longest diameter

		Var[][] x = array("x", size(d, d), (i, j) -> dom(range(s, s + gap)).when(j < d - Math.abs(d / 2 - i)),
				"x represents the hexagon; on row x[i], only the first n - |n/2 - i| cells are useful (here, n = " + d + ").");

		allDifferent(x);
		forall(range(d), i -> sum(x[i], EQ, magic)).note("all rows sum to the magic value");
		forall(range(d), i -> sum(scopeForDiagonal(x, i, true), EQ, magic)).note("all right-sloping diagonals sum to the magic value");
		forall(range(d), i -> sum(scopeForDiagonal(x, i, false), EQ, magic)).note("all left-sloping diagonals sum to the magic value");

		block(() -> {
			lessThan(x[0][0], x[0][n - 1]);
			lessThan(x[0][0], x[n - 1][d - 1]);
			lessThan(x[0][0], x[d - 1][n - 1]);
			lessThan(x[0][0], x[d - 1][0]);
			lessThan(x[0][0], x[n - 1][0]);
			lessThan(x[0][n - 1], x[n - 1][0]);
		}).tag(SYMMETRY_BREAKING);
	}
}
