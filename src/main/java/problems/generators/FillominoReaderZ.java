/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import problems.ReaderFile.ReaderDzn;
import problems.g3_pattern.Fillomino;
import utility.Kit;

public class FillominoReaderZ extends Fillomino implements ReaderDzn {

	void data() {
		int nRows = nextInt();
		int nCols = nextInt();
		int[][] puzzle = nextInt2D();

		System.out.println(nRows + " " + nCols + "\n" + Kit.join(puzzle));
		setDataValues(puzzle);
	}

}
