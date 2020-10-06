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
import problems.g3_pattern.MagicSquare;

public class MagicSquare_Parser extends MagicSquare implements ReaderTxt {

	void data() {
		int n = nextInt();
		int[][] clues = new int[n][n];
		int nClues = nextInt();
		for (int i = 0; i < nClues; i++)
			clues[nextInt() - 1][nextInt() - 1] = nextInt();
		setDataValues(n, (Object) clues);
	}
}
