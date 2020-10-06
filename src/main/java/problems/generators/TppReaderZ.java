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
import problems.g4_world.TravelingPurchaser;

// java abscon.Resolution problems.generators.TppReaderZ tpp-7-5-30-1.dzn -ev -f=cop => 124 in 2s
public class TppReaderZ extends TravelingPurchaser implements ReaderDzn {

	void data() {
		int nProducts = nextInt();
		int nCities = nextInt();
		nextInt(); // maxDist
		nextInt(); // maxPrice
		int[][] distances = nextInt2D();
		int[][] prices = nextInt2D();
		prices = transpose(prices);
		control(nProducts == prices.length && nCities == distances.length && Stream.of(prices).allMatch(t -> IntStream.of(t).allMatch(v -> v > 0)));
		setDataValues(distances, (Object) prices);
	}
}