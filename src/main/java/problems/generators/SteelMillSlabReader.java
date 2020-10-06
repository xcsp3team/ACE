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

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.SteelMillSlab;

public class SteelMillSlabReader extends SteelMillSlab implements ReaderTxt {

	void data() {
		int[] slabCapacities = Utilities.splitToInts(nextLine());
		nextInt(); // nColors
		int nOrders = nextInt();
		Stream<Object> orders = IntStream.range(0, nOrders).mapToObj(i -> imp().buildInternClassObject("Order", nextInt(), nextInt()));
		setDataValues(slabCapacities, orders);
	}
}
