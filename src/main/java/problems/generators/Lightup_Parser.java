/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.Lightup;

public class Lightup_Parser extends Lightup implements ReaderTxt {

	void data() {
		int nRows = nextInt();
		next();
		int nCols = nextInt();
		int[][] grid = new int[nRows][nCols];
		for (int i = 0; i < nRows; i++)
			for (int j = 0; j < nCols; j++) {
				String token = next();
				grid[i][j] = token.equals("a") ? 5 : token.equals("-") ? -1 : Integer.parseInt(token);
			}
		setDataValues(grid);
	}

}