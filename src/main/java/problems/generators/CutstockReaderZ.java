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

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderDzn;
import problems.g3_pattern.Cutstock;

// See From High-Level Model to Branch-and-Price Solution in G12
// In the cutting stock problem, we are given N items with associated lengths and demands. 
// We are further given stock pieces with length L and an upper bound K on the number of required stock pieces for satisfying the demand (a trivial upper bound is the sum over all the demands). 
//The following Zinc model corresponds to the formulation by Kantorovich
public class CutstockReaderZ extends Cutstock implements ReaderDzn {

	void data() {
		int nItems = nextInt();
		int pieceLength = nextInt();
		int[] itemLengths = nextInt1D();
		int[] itemDemands = nextInt1D();
		Utilities.control(nItems == itemLengths.length && nItems == itemDemands.length, "");
		int nPieces = IntStream.range(0, nItems).map(i -> (itemDemands[i] / (pieceLength / itemLengths[i])) + 1).sum();
		Stream<Object> items = IntStream.range(0, nItems).mapToObj(i -> buildInternClassObject("Item", itemLengths[i], itemDemands[i]));
		setDataValues(nPieces, pieceLength, items);
	}
}
