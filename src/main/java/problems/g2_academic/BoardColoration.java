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

/**
 * All squares of a board of a specified size (specified numbers of rows and columns) must be colored with the minimum number of colors. The four
 * corners of any rectangle inside the board must not be assigned the same color.
 */
public class BoardColoration implements ProblemAPI {

	int nRows;
	int nCols;

	@Override
	public void model() {
		Var[][] x = array("x", size(nRows, nCols), dom(range(nRows * nCols)), "x[i][j] is the color at row i and column j");

		forall(range(nRows).range(nRows).range(nCols).range(nCols), (i1, i2, j1, j2) -> {
			if (i1 < i2 && j1 < j2)
				notAllEqual(x[i1][j1], x[i1][j2], x[i2][j1], x[i2][j2]);
		}).note("at least two corners of different colors for any rectangle inside the board");
		lexMatrix(x, INCREASING).tag(SYMMETRY_BREAKING);

		minimize(MAXIMUM, x);
	}
}