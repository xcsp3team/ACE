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
import org.xcsp.modeler.api.ProblemAPI;

// https://www.puzzle-light-up.com/ or akari
// https://en.wikipedia.org/wiki/Light_Up_(puzzle)
public class Lightup implements ProblemAPI {

	int[][] grid; // grid[i][j] is -1 for a white cell, or a clue between 0 and 4, or the value 5 for a black cell

	Var[] sequenceScope(Var[][] x, int i, int j, boolean horizontal) {
		List<Var> list = new ArrayList<>();
		if (horizontal) {
			if (j == 0 || grid[i][j - 1] != -1 && grid[i][j] == -1)
				while (j < grid[i].length && grid[i][j] == -1)
					list.add(x[i][j++]);
		} else {
			if (i == 0 || grid[i - 1][j] != -1 && grid[i][j] == -1)
				while (i < grid.length && grid[i][j] == -1)
					list.add(x[i++][j]);
		}
		return list.size() > 1 ? list.toArray(new Var[0]) : null;
	}

	Var[] fullScope(Var[][] x, int i, int j) {
		if (grid[i][j] != -1)
			return null;
		List<Var> list = new ArrayList<>();
		int base = j;
		while (base >= 0 && grid[i][base] == -1)
			base--;
		for (int jj = base + 1; jj < grid[i].length && grid[i][jj] == -1; jj++)
			list.add(x[i][jj]);
		base = i;
		while (base >= 0 && grid[base][j] == -1)
			base--;
		for (int ii = base + 1; ii < grid.length && grid[ii][j] == -1; ii++)
			if (ii != i)
				list.add(x[ii][j]);
		return list.toArray(new Var[0]);
	}

	Var[] sideScope(Var[][] x, int i, int j) {
		List<Var> list = new ArrayList<>();
		if (i > 0 && grid[i - 1][j] == -1)
			list.add(x[i - 1][j]);
		if (i < grid.length - 1 && grid[i + 1][j] == -1)
			list.add(x[i + 1][j]);
		if (j > 0 && grid[i][j - 1] == -1)
			list.add(x[i][j - 1]);
		if (j < grid[i].length - 1 && grid[i][j + 1] == -1)
			list.add(x[i][j + 1]);
		return list.toArray(new Var[0]);
	}

	@Override
	public void model() {
		int nRows = grid.length, nCols = grid[0].length;
		Var[][] x = array("x", size(nRows, nCols), (i, j) -> dom(0, 1).when(grid[i][j] == -1), "x[i][j] is 1 iff a light bulb is put at row i and col j");

		forall(range(nRows).range(nCols), (i, j) -> {
			Var[] scp = sequenceScope(x, i, j, true);
			if (scp != null)
				atMost1(scp, takingValue(1));
		}).note("at most 1 bulb on each maximal sequence of white cells on rows");
		forall(range(nRows).range(nCols), (i, j) -> {
			Var[] scp = sequenceScope(x, i, j, false);
			if (scp != null)
				atMost1(scp, takingValue(1));
		}).note("at most 1 bulb on each maximal sequence of white cells on columns");
		forall(range(nRows).range(nCols), (i, j) -> {
			Var[] scp = fullScope(x, i, j);
			if (scp != null)
				atLeast1(scp, takingValue(1));
		});
		forall(range(nRows).range(nCols), (i, j) -> {
			if (0 <= grid[i][j] && grid[i][j] <= 4)
				exactly(sideScope(x, i, j), takingValue(1), grid[i][j]);
		}).tag(CLUES);

	}
}