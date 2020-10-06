/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import java.util.function.Predicate;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

// java abscon.Resolution problems.patt.StillLife 1 8 8 -ev -f=cop -valh=Last -sing=Last
// java abscon.Resolution problems.patt.StillLife 2 10 10 -ev -f=cop -valh=Last -sing=Last -os=decreasing
public class StillLife implements ProblemAPI {

	int n, m;

	@NotData
	Predicate<int[]> p = x -> {
		int s1 = x[0] + x[1] + x[2] + x[3] + x[5] + x[6] + x[7] + x[8];
		int s2 = x[0] * x[2] + x[2] * x[8] + x[8] * x[6] + x[6] * x[0] + x[1] + x[3] + x[5] + x[7];
		int s3 = x[1] + x[3] + x[5] + x[7];
		return (x[4] != 1 || s1 >= 2) && (x[4] != 1 || s1 <= 3) && (x[4] != 0 || s1 != 3) && (x[4] != 1 || s2 > 1 || x[9] >= 1)
				&& (x[4] != 1 || s2 > 0 || x[9] >= 2) && (x[4] != 0 || s3 < 4 || x[9] >= 2) && (x[4] != 0 || s3 > 1 || x[9] >= 1)
				&& (x[4] != 0 || s3 > 0 || x[9] >= 2);
	};

	@Override
	public void model() {
		Table conflicts = table(NEGATIVE).add(1, 1, 1);

		if (!modelVariant("wastage")) {
			Var[][] x = array("x", size(n, m), dom(0, 1), "x[i][j] is 1 iff the cell at row i and col j is alive");
			Var[][] a = array("a", size(n, m), dom(range(9)), "a[i][j] is the number of alive neighbours");

			forall(range(n).range(m),
					(i, j) -> sum(select(x, (k, l) -> i - 1 <= k && k <= i + 1 && j - 1 <= l && l <= j + 1 && (k != i || l != j)), EQ, a[i][j]))
							.note("computing the numbers of alive neighbours");
			Table table = table("(0,0)(1, 0)(2,0)(2,1)(3,1)(4,0)(5,0)(6,0)(7,0)(8,0)");
			forall(range(n).range(m), (i, j) -> extension(vars(a[i][j], x[i][j]), table)).note("imposing rules of the game");

			block(() -> {
				slide(x[0], range(m - 2), i -> extension(vars(x[0][i], x[0][i + 1], x[0][i + 2]), conflicts));
				slide(x[n - 1], range(m - 2), i -> extension(vars(x[n - 1][i], x[n - 1][i + 1], x[n - 1][i + 2]), conflicts));
				slide(columnOf(x, 0), range(n - 2), i -> extension(vars(x[i][0], x[i + 1][0], x[i + 2][0]), conflicts));
				slide(columnOf(x, m - 1), range(n - 2), i -> extension(vars(x[i][m - 1], x[i + 1][m - 1], x[i + 2][m - 1]), conflicts));
			}).note("imposing rules for ensuring valid dead cells around the board");

			if (n == m)
				block(() -> {
					greaterEqual(x[0][0], x[n - 1][n - 1]);
					greaterEqual(x[0][n - 1], x[n - 1][0]);
				}).tag(SYMMETRY_BREAKING);

			maximize(SUM, vars(x));
		} else {
			control(n == m);
			Var[][] x = array("x", size(n + 2, n + 2), dom(0, 1), "x[i][j] is 1 iff the cell at row i and col j is alive (note that there is a border)");
			Var[][] w = array("w", size(n + 2, n + 2), dom(0, 1, 2), "w[i][j] is the wastage for the cell at row i and col j");
			Var[] ws = array("ws", size(n + 2), dom(range(2 * (n + 2) * (n + 2) + 1)), "ws[i] is the wastage sum for cells at row i");
			Var z = var("z", dom(range(n * n + 1)), "z is the number of alive cells");

			// block(() -> {
			// instantiation(x[0], takingValue(0));
			// instantiation(x[n + 1], takingValue(0));
			// instantiation(columnOf(x, 0), takingValue(0));
			// instantiation(columnOf(x, n + 1), takingValue(0));
			// }).note("cells at the border are assumed to be dead");

			instantiation(vars(x[0], x[n + 1], columnOf(x, 0), columnOf(x, n + 1)), takingValue(0)).note("cells at the border are assumed to be dead");

			block(() -> {
				slide(x[1], range(n), j -> extension(vars(x[1][j], x[1][j + 1], x[1][j + 2]), conflicts));
				slide(x[n], range(n), j -> extension(vars(x[n][j], x[n][j + 1], x[n][j + 2]), conflicts));
				slide(columnOf(x, 1), range(n), i -> extension(vars(x[i][1], x[i + 1][1], x[i + 2][1]), conflicts));
				slide(columnOf(x, n), range(n), i -> extension(vars(x[i][n], x[i + 1][n], x[i + 2][n]), conflicts));
			}).note("ensuring that cells at the border remain dead");

			int[][] tuples = allCartesian(vals(2, 2, 2, 2, 2, 2, 2, 2, 2, 3), p);
			forall(range(1, n + 1).range(1, n + 1), (i, j) -> {
				Var[] neighbors = select(x, range(i - 1, i + 2).range(j - 1, j + 2));
				extension(vars(neighbors, w[i][j]), tuples);
			}).note("still life + wastage constraints");

			block(() -> {
				forall(range(1, n + 1), j -> equal(add(w[0][j], x[1][j]), 1));
				forall(range(1, n + 1), j -> equal(add(w[n + 1][j], x[n][j]), 1));
				forall(range(1, n + 1), i -> equal(add(w[i][0], x[i][1]), 1));
				forall(range(1, n + 1), i -> equal(add(w[i][n + 1], x[i][n]), 1));
			}).note("managing wastage on the border");

			forall(range(n + 2), i -> sum(i == 0 ? w[0] : vars(ws[i - 1], w[i]), EQ, ws[i])).note("summing wastage");
			sum(vars(z, ws[n + 1]), vals(4, 1), EQ, 2 * n * n + 4 * n).note("setting the value of the objective");
			forall(range(n + 1), i -> greaterEqual(sub(ws[n + 1], ws[i]), 2 * ((n - i) / 3) + n / 3)).tag(REDUNDANT_CONSTRAINTS);

			maximize(z).note("maximizing the number of alive cells");
		}
	}
}

// Var[] neighbors = select(x, (k, l) -> i - 1 <= k && k <= i + 1 && j - 1 <= l && l <= j + 1);
