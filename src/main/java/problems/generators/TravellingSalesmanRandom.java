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

import problems.g3_pattern.TravelingSalesman;
import utility.Kit;

public class TravellingSalesmanRandom extends TravelingSalesman {

	void data() {
		int nCities = imp().askInt("Number of cities");
		int mapSize = imp().askInt("Size (width and height) of the map");
		int seed = imp().askInt("Seed");
		int[] cityPositions = Kit.pickDifferentValues(nCities, mapSize * mapSize, new Random(seed));
		int[][] distances = range(nCities).range(nCities).map((i, j) -> {
			int rowDistance = Math.abs(cityPositions[i] / mapSize - cityPositions[j] / mapSize);
			int colDistance = Math.abs(cityPositions[i] % mapSize - cityPositions[j] % mapSize);
			int distance = (int) Math.round(Math.sqrt((rowDistance * rowDistance + colDistance * colDistance)));
			return distance;
		});
		imp().setDataValues(distances);
	}

}