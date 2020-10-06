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

import problems.ReaderFile.ReaderDzn;
import problems.g4_world.SolitaireBattleship;

public class SolitaireBattleshipReaderZ extends SolitaireBattleship implements ReaderDzn {

	void data() {
		int height = nextInt();
		int width = nextInt();
		int maxShip = nextInt();
		int[] ships = nextInt1D();
		Utilities.control(height == width && maxShip == ships.length, "Not valid parameters");
		Stream<Object> fleet = IntStream.range(0, ships.length).filter(i -> ships[i] != 0)
				.mapToObj(i -> imp().buildInternClassObject("ShipCategory", i + 1, ships[i]));
		int[][] m = nextInt2D();
		Utilities.control(Stream.of(m).allMatch(t -> IntStream.of(t).allMatch(v -> v == 0)), "Hint detected");
		Object hints = null;
		int[] rowSums = nextInt1D();
		int[] colSums = nextInt1D();
		setDataValues(fleet, rowSums, colSums, hints);
	}

}
