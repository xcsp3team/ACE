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
import org.xcsp.common.enumerations.EnumerationCartesian;
import org.xcsp.modeler.api.ProblemAPI;

// order 4 :7040 solutions
// java abscon.Resolution problems.puzz.MagicSquare -data=[4,-]  ; - means no clue
public class MagicSquare implements ProblemAPI {
	int n;
	int[][] clues;

	@Override
	public void model() {
		int magic = n * (n * n + 1) / 2;

		Var[][] x = array("x", size(n, n), dom(rangeClosed(1, n * n)), "x[i][j] is the value at row i and column j of the magic square");

		allDifferent(x);

		if (modelVariant("")) {
			forall(range(n), i -> sum(x[i], EQ, magic));
			forall(range(n), j -> sum(columnOf(x, j), EQ, magic));
			block(() -> {
				sum(diagonalDown(x), EQ, magic);
				sum(diagonalUp(x), EQ, magic);
			}).tag(DIAGONALS);
		}
		if (modelVariant("ext")) {
			int[][] tuples = EnumerationCartesian.tuplesWithDiffValuesSummingTo(magic, n * n, n, 1);
			forall(range(n), i -> extension(x[i], tuples));
			forall(range(n), j -> extension(columnOf(x, j), tuples));
			block(() -> {
				extension(diagonalDown(x), tuples);
				extension(diagonalUp(x), tuples);
			}).tag(DIAGONALS);
		}
		if (modelVariant("mdd")) {
			forall(range(n), i -> sum(x[i], IN, rangeClosed(magic, magic)));
			forall(range(n), j -> sum(columnOf(x, j), IN, rangeClosed(magic, magic)));
			block(() -> {
				sum(diagonalDown(x), IN, rangeClosed(magic, magic));
				sum(diagonalUp(x), IN, rangeClosed(magic, magic));
			}).tag(DIAGONALS);
		}
		instantiation(x, takingValues(clues), onlyOn((i, j) -> clues[i][j] != 0)).tag(CLUES).note("respecting specified clues (if any)");
	}
}
