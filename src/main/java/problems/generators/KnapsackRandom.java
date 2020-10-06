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

import problems.g3_pattern.Knapsack;

public class KnapsackRandom extends Knapsack {

	void data() {
		int nObjects = imp().askInt("Number of objects");
		int capacity = imp().askInt("Capacity");
		int seed = imp().askInt("Seed", "%02d");
		int MAX_PROFIT = 100; // hard coding

		Random rand = new Random(seed);
		int[] weights = valuesFrom(range(nObjects), i -> 1 + rand.nextInt(capacity / 4));
		int[] values = valuesFrom(range(nObjects), i -> 1 + rand.nextInt(MAX_PROFIT));
		Object items = range(nObjects).mapToObj(i -> imp().buildInternClassObject("Item", weights[i], values[i]));
		imp().setDataValues(capacity, items);
	}
}
