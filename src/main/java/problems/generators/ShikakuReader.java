/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.stream.Stream;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.Shikaku;

public class ShikakuReader extends Shikaku implements ReaderTxt {
	void data() {
		int nRows = nextInt();
		int nCols = scanner().skip("\\s+x\\s+").nextInt();
		int nRooms = nextInt();
		int[][] rooms = new int[nRooms][];
		range(nRooms).execute(i -> rooms[i] = tuple(nextInt(), nextInt(), imp().fileScanner().skip("\\s+:\\s+").nextInt()));
		control(Stream.of(rooms).mapToInt(r -> r[2]).reduce(0, (s, t) -> s + t) == nRows * nCols);
		setDataValues(nRows, nCols, Stream.of(rooms).map(r -> buildInternClassObject("Room", r[0], r[1], r[2])));
	}
}
