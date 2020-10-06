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

import problems.ReaderFile.ReaderDzn;
import problems.g3_pattern.Mario;

// java abscon.Resolution problems.generators.MarioReaderZ mario_n_medium_2.dzn -ev -f=cop -os=decreasing => 1053 in 395s
public class MarioReaderZ extends Mario implements ReaderDzn {

	void data() {
		nextInt(); // nHouses
		int marioHouse = nextInt() - 1; // -1 because we start at 0
		int luigiHouse = nextInt() - 1; // -1 because we start at 0
		int fuelLimit = nextInt();
		nextInt(); // goldTotalAmount
		int[][] fuelConsumption = nextInt2D();
		int[] goldInHouse = nextInt1D();
		Stream<Object> houses = IntStream.range(0, goldInHouse.length).mapToObj(i -> buildInternClassObject("House", fuelConsumption[i], goldInHouse[i]));
		setDataValues(marioHouse, luigiHouse, fuelLimit, houses);
	}
}
