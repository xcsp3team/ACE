/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g0_school;

import java.util.Random;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class Squaro implements ProblemAPI {
	int nRows, nCols;
	int[][] cardinalities;

	void data() {
		nRows = imp().askInt("Number of rows");
		nCols = imp().askInt("Number of columns");
		int seed = imp().askInt("Seed");

		Random rand = new Random(seed);
		int[][] solution = new int[nRows + 1][nCols + 1];
		for (int i = 0; i < solution.length; i++)
			for (int j = 0; j < solution[i].length; j++)
				solution[i][j] = rand.nextInt(2);
		cardinalities = new int[nRows][nCols];
		for (int i = 0; i < cardinalities.length; i++)
			for (int j = 0; j < cardinalities[i].length; j++)
				cardinalities[i][j] = solution[i][j] + solution[i][j + 1] + solution[i + 1][j] + solution[i + 1][j + 1]; // random.nextInt(5);
		// System.out.println(Toolkit.buildStringFromInts(cardinalities));
	}

	@Override
	public void model() {
		Var[][] x = array("x", size(nRows + 1, nCols + 1), dom(0, 1));
		forall(range(nRows).range(nCols), (i, j) -> sum(vars(x[i][j], x[i][j + 1], x[i + 1][j], x[i + 1][j + 1]), EQ, cardinalities[i][j]));
	}
}