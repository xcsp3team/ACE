/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.ArrayList;
import java.util.List;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.enumerations.EnumerationCartesian;
import org.xcsp.modeler.api.ProblemAPI;

public class Kakuro implements ProblemAPI {

	int nRows, nCols;
	Clue[][] clues;

	class Clue {
		int x, y;
	}

	private Var[] horScope(Var[][] x, int i, int j) {
		assert clues[i][j].x > 0;
		List<Var> list = new ArrayList<>();
		for (int k = j + 1; k < nCols && clues[i][k].x == 0; k++)
			list.add(x[i][k]);
		return list.toArray(new Var[0]);
	}

	private Var[] verScope(Var[][] x, int i, int j) {
		assert clues[i][j].y > 0;
		List<Var> list = new ArrayList<>();
		for (int k = i + 1; k < nRows && clues[k][j].y == 0; k++)
			list.add(x[k][j]);
		return list.toArray(new Var[0]);
	}

	@Override
	public void model() {
		Var[][] x = array("x", size(nRows, nCols), (i, j) -> dom(rangeClosed(1, 9)).when(clues[i][j].x == 0 && clues[i][j].y == 0),
				"x[i][j] is the value put at row i and column j");

		if (modelVariant("")) {
			forall(range(nRows).range(nCols), (i, j) -> {
				if (clues[i][j].x > 0) {
					Var[] scp = horScope(x, i, j);
					sum(scp, EQ, clues[i][j].x);
					allDifferent(scp);
				}
			});
			forall(range(nRows).range(nCols), (i, j) -> {
				if (clues[i][j].y > 0) {
					Var[] scp = verScope(x, i, j);
					sum(scp, EQ, clues[i][j].y);
					allDifferent(scp);
				}
			});
		}
		if (modelVariant("table")) {
			forall(range(nRows).range(nCols), (i, j) -> {
				if (clues[i][j].x > 0) {
					Var[] scp = horScope(x, i, j);
					extension(scp, EnumerationCartesian.tuplesWithDiffValuesSummingTo(clues[i][j].x, 9, scp.length, 1));
				}
			});
			forall(range(nRows).range(nCols), (i, j) -> {
				if (clues[i][j].y > 0) {
					Var[] scp = verScope(x, i, j);
					extension(scp, EnumerationCartesian.tuplesWithDiffValuesSummingTo(clues[i][j].y, 9, scp.length, 1));
				}
			});
		}
	}
}

// int[][] verLengths = IntStream.range(0, nRows).mapToObj(i -> IntStream.range(0, nCols).map(j -> computeVerLength(i, j)).toArray())
// .toArray(int[][]::new);
