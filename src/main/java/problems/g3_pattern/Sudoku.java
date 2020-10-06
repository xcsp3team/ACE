/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.Arrays;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

public class Sudoku implements ProblemAPI {

	int n; // order of the grid (typically, 9)
	int[][] clues; // if not 0, clues[i][j] is a value imposed at row i and col j

	@Override
	public void model() {
		int base = (int) Math.sqrt(n);

		Var[][] x = array("x", size(n, n), dom(rangeClosed(1, n)), "x[i][j] is the value in cell at row i and col j.");

		if (modelVariant("")) {
			allDifferentMatrix(x).note("imposing distinct values on each row and each column");
			forall(range(0, n, base).range(0, n, base), (i, j) -> allDifferent(select(x, range(i, i + base).range(j, j + base))))
					.note("imposing distinct values on each block").tag(BLOCKS);
		}

		if (modelVariant("table")) {
			int[][] permutations = allPermutations(rangeClosed(1, n).toArray());
			Arrays.sort(permutations, Utilities.lexComparatorInt);
			block(() -> {
				forall(range(n), i -> extension(x[i], permutations));
				forall(range(n), j -> extension(columnOf(x, j), permutations));
			}).note("imposing distinct values on each row and each column");
			forall(range(0, n, base).range(0, n, base), (i, j) -> extension(select(x, range(i, i + base).range(j, j + base)), permutations))
					.note("imposing distinct values on each block").tag(BLOCKS);
		}

		if (clues != null)
			instantiation(x, clues, (i, j) -> clues[i][j] != 0).note("imposing clues").tag(CLUES);
	}
}
