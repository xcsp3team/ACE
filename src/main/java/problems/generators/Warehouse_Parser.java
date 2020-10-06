/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import static org.xcsp.common.Utilities.splitToInt;
import static org.xcsp.common.Utilities.splitToInts;

import java.util.stream.IntStream;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.Warehouse;

// Problem defined at http://csplib.org/Problems/prob034/
public class Warehouse_Parser extends Warehouse implements ReaderTxt {
	void data() {
		int nWarehouses = splitToInt(nextLine(), "[nN]bW=|;");
		int nStores = splitToInt(nextLine(), "[nN]bS=|;");
		int fixedCost = splitToInt(nextLine(), "fixed=|;");
		String line = nextLine();
		int[] warehouseCapacities = null;
		if (line.startsWith("cap")) {
			warehouseCapacities = splitToInts(line, "capacity=\\[|,\\s|\\];");
			nextLine();
		} else
			warehouseCapacities = IntStream.range(0, nWarehouses).map(i -> nStores).toArray();

		int[][] storeSupplyCosts = range(nStores).mapToObj(i -> splitToInts(nextLine(), "(\\s|\\[|\\]|,)+"));
		setDataValues(fixedCost, warehouseCapacities, storeSupplyCosts);
	}
}
