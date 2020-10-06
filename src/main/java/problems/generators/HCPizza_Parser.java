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

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.HCPizza;

// java AbsCon problems.generators.HCPizzaReader ~/instances/hashCode/2018Qualif/small.in
public class HCPizza_Parser extends HCPizza implements ReaderTxt {

	void data() {
		int nRows = nextInt();
		nextInt(); // nCols
		int minIngredients = nextInt();
		int maxSize = nextInt();
		nextLine();
		int[][] pizza = IntStream.range(0, nRows).mapToObj(i -> Stream.of(nextLine().split("")).mapToInt(s -> s.equals("M") ? 0 : 1).toArray())
				.toArray(int[][]::new);
		setDataValues(minIngredients, maxSize, pizza);
	}
}
