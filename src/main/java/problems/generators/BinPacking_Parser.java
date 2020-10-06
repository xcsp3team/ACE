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

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.BinPacking;

//optimum 5 for Scholl/skj1/n1c1w4a.txt
public class BinPacking_Parser extends BinPacking implements ReaderTxt {

	void data() {
		int nItems = nextInt();
		int binCapacity = nextInt();
		int[] itemWeights = IntStream.range(0, nItems).map(i -> nextInt()).sorted().toArray();
		setDataValues(binCapacity, itemWeights);
	}
}
