/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.Nonogram;

public class Nonogram_Parser extends Nonogram implements ReaderTxt {

	void data() {
		int nRows = nextInt();
		int nCols = nextInt();
		Stream<int[]> rowPatterns = IntStream.range(0, nRows).mapToObj(i -> IntStream.range(0, nextInt()).map(j -> nextInt()).toArray());
		Stream<int[]> colPatterns = IntStream.range(0, nCols).mapToObj(i -> IntStream.range(0, nextInt()).map(j -> nextInt()).toArray());
		setDataValues(rowPatterns, colPatterns);
	}
}
