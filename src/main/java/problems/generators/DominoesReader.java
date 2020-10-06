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
import problems.g3_pattern.Dominoes;

public class DominoesReader extends Dominoes implements ReaderTxt {
	void data() {
		int nRows = nextInt();
		next(); // because the presence of character x
		int nCols = nextInt();
		control(nCols == nRows + 1);
		int[][] grid = range(nRows).range(nCols).map((i, j) -> nextInt());
		setDataValues(grid);
	}

}
