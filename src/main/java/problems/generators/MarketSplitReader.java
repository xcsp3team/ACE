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

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.MarketSplit;

public class MarketSplitReader extends MarketSplit implements ReaderTxt {

	void data() {
		int e = nextInt(), n = nextInt();
		Utilities.control(n == 10 * (e - 1), "The relationship between n and e is bad");
		int[][] coeffs = new int[e][n];
		int[] limits = new int[e];
		for (int i = 0; i < coeffs.length; i++) {
			coeffs[i] = range(n).map(j -> nextInt());
			limits[i] = nextInt();
		}
		Stream<Object> ctrs = IntStream.range(0, e).mapToObj(i -> buildInternClassObject("Ctr", coeffs[i], limits[i]));
		setDataValues(n, ctrs);
	}
}