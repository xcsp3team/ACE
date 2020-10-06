/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.stream.Stream;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.ProgressiveParty;

public class ProgressiveParty_Parser extends ProgressiveParty implements ReaderTxt {

	void data() {
		int nBoats = nextInt();
		int nPeriods = nextInt();
		int[][] m = range(nBoats).range(3).map((i, j) -> nextInt());
		Stream<Object> boats = Stream.of(m).map(t -> imp().buildInternClassObject("Boat", t[1], t[2]));
		setDataValues(nPeriods, boats);
	}

}
