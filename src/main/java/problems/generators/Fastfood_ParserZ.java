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
import problems.g3_pattern.Fastfood;

//java abscon.Resolution problems.patt.Fastfood ~/instances/minizinc-benchmarks-master/fast-food/ff01.dzn -f=cop => opt=3050
public class Fastfood_ParserZ extends Fastfood implements ReaderDzn {

	void data() {
		int nRestaurants = nextInt();
		String[] names = nextString1D();
		int[] positions = nextInt1D();
		control(nRestaurants == names.length && nRestaurants == positions.length);
		Stream<Object> restaurants = IntStream.range(0, names.length).mapToObj(i -> buildInternClassObject("Restaurant", names[i], positions[i]));
		int nDepots = nextInt();
		setDataValues(nDepots, restaurants);
	}
}