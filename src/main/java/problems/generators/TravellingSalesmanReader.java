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
import problems.g3_pattern.TravelingSalesman;
import utility.Kit;

public class TravellingSalesmanReader extends TravelingSalesman implements ReaderTxt {

	void data() {
		int nCities = nextInt();
		int[][] distances = range(nCities).range(nCities).map((i, j) -> nextInt());
		System.out.println("n=" + nCities + " " + Kit.join(distances));
		setDataValues(distances);
	}

}