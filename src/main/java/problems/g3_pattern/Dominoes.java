/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

public class Dominoes implements ProblemAPI {

	int[][] grid;

	@NotData
	int nRows, nCols;

	private XNodeParent<IVar> adjacencyPredicate(Var x, Var y) {
		// XNodeParent<IVar> verAdjacency = or(eq(x, add(y, nCols)), eq(y, add(x, nCols)));
		// XNodeParent<IVar> horAdjacency = or(and(eq(x, add(y, 1)), ne(mod(x, nCols), 0)), and(eq(y, add(x, 1)), ne(mod(y, nCols), 0)));
		return or(eq(x, add(y, nCols)), eq(y, add(x, nCols)), and(eq(x, add(y, 1)), ne(mod(x, nCols), 0)), and(eq(y, add(x, 1)), ne(mod(y, nCols), 0)));
	}

	private int[] positionsOf(int value) {
		return valuesFrom(range(nRows).range(nCols), (i, j) -> grid[i][j] == value ? i * nCols + j : null);
	}

	@Override
	public void model() {
		nRows = grid.length;
		nCols = grid[0].length;
		int nValues = nRows;

		Var[][] x = array("x", size(nValues, nValues), (i, j) -> dom(range(nRows * nCols)).when(i <= j),
				"x[i][j] concerns the domino (having values) i-j; this is the position of the value i in the grid for this domino");
		Var[][] y = array("y", size(nValues, nValues), (i, j) -> dom(range(nRows * nCols)).when(i <= j),
				"y[i][j] concerns the domino (having values) i-j; this is the position of the value j in the grid for this domino");

		allDifferent(vars(x, y)).note("each part of each domino in a different cell");

		forall(range(nValues), i -> forall(range(i, nValues), j -> {
			belong(x[i][j], set(positionsOf(i)));
			belong(y[i][j], set(positionsOf(j)));
		})).note("unary constraints");

		forall(range(nValues), i -> forall(range(i, nValues), j -> {
			intension(adjacencyPredicate(x[i][j], y[i][j]));
		})).note("adjacency constraints");
	}

	// return IntStream.range(0, nRows).flatMap(i -> IntStream.range(0, nCols).filter(j -> grid[i][j] == value).map(j -> i * nCols +
	// j)).toArray();

	// @Override
	// public void prettyDisplay(String[] values) {
	// // int nbRows = gridValues.length, nbColumns = gridValues[0].length;
	// BorderArray ba = new BorderArray(nRows, nCols);
	// for (int i = 0; i < nRows; i++)
	// for (int j = i; j < nCols; j++) {
	// int val0 = Integer.parseInt(values[i * nRows + j]);
	// int val1 = Integer.parseInt(values[nRows * nCols + i * nRows + j]);
	// // Var[] domino = x[i][j];
	// int row1 = val0 / nCols, row2 = val1 / nCols;
	// int col1 = val0 % nCols, col2 = val1 % nCols;
	// ba.writeBorder(Math.min(col1, col2), Math.max(col1, col2) + 1, Math.min(row1, row2), Math.max(row1, row2) + 1);
	// }
	// for (int i = 0; i < nRows; i++)
	// for (int j = 0; j < nCols; j++)
	// ba.writeValue(i, j, grid[i][j]);
	// System.out.println(ba);
	// }
}