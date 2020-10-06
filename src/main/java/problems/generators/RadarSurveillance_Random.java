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

import problems.g4_world.RadarSurveillance;
import tools.random.RandomGeneration.RandomGenerationProp;
import tools.random.RandomGeneration.RandomGenerationProp.TypeList;

public class RadarSurveillance_Random extends RadarSurveillance {
	private static final int[] seedsSAT_8_24_3_2 = IntStream.of(0, 4, 6, 8, 10, 15, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 35, 37, 38, 40, 42, 43, 45, 49, 50,
			55, 56, 71, 74, 75, 78, 79, 81, 92, 95, 96, 98, 100, 101, 104, 105, 106, 107, 112, 116, 117, 118, 119, 120, 121).toArray();

	private static final int[] seedsUNSAT_8_24_3_2 = IntStream.of(1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 25, 32, 33, 34, 36, 39, 41, 44, 46, 47,
			48, 51, 52, 53, 54, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 72, 73, 76, 77, 80, 82).toArray();

	private static final int[] seeds = IntStream.of(6, 8, 11, 22, 72, 157, 172, 185, 202, 217, 224, 253, 274, 275, 312, 323, 356, 359, 366, 392, 448, 454, 491,
			507, 572, 576, 577, 587, 614, 630, 675, 677, 683, 714, 729, 757, 839, 840, 850, 870, 876, 902, 912, 1029, 1030, 1040, 1061, 1068, 1072, 1090)
			.toArray();

	void data() {
		int mapSize = imp().askInt("map size");
		int nRadars = imp().askInt("number of radars");
		int maxCoverage = imp().askInt("maximum coverage");
		int nInsignificantCells = imp().askInt("number of insignificant cells");
		int series = imp().askInt("series", range(0, 4), "");
		int seed = imp().askInt("seed", "%02d");
		seed = series == 0 ? seed : series == 1 ? seedsSAT_8_24_3_2[seed] : series == 2 ? seedsUNSAT_8_24_3_2[seed] : seeds[seed];
		RandomGenerationProp r = new RandomGenerationProp(mapSize, 2, seed);
		int[][] radars = r.selectTuples(nRadars, TypeList.UNSTRUCTURED, false, true);
		int[][] insignificantCells = r.selectTuples(nInsignificantCells, TypeList.UNSTRUCTURED, false, true);
		imp().setDataValues(mapSize, maxCoverage, radars, insignificantCells);
	}

}