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
import problems.g3_pattern.Sudoku;

public class Sudoku_Parser extends Sudoku implements ReaderTxt {

	void data() {
		int n = 9; // to be changed
		Object clues = range(n).range(n).map((i, j) -> nextInt());
		setDataValues(n, clues);
	}

}
