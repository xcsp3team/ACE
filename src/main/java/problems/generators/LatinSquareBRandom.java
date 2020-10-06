/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.Random;

import problems.g3_pattern.LatinSquareB;
import utility.Kit;

class LatinSquareBRandom extends LatinSquareB {

	void data() {
		int n = imp().askInt("Order");
		int nClues = imp().askInt("Number of preassigned cells", range(n * n));
		int seed = imp().askInt("Seed");

		Random random = new Random(seed);
		int[] t = Kit.pickDifferentValues(nClues, n * n, random);
		Object clues = range(nClues).mapToObj(i -> imp().buildInternClassObject("Clue", t[i] / n, t[i] % n, random.nextInt(n)));
		imp().setDataValues(n, clues);
	}
}