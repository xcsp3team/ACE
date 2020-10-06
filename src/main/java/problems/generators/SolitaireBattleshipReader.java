/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.AbstractMap.SimpleEntry;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.SolitaireBattleship;

public class SolitaireBattleshipReader extends SolitaireBattleship implements ReaderTxt {

	void data() {
		scanner(); // required for asking the filname
		int num = imp().askInt("num", "%03d");
		String line = null;
		for (int cnt = 0; cnt <= num; cnt++) {
			line = nextLine();
			while (line != null && !line.startsWith("problem"))
				line = nextLine();
		}
		int id = Integer.parseInt(line.substring(line.indexOf("(") + 1, line.length() - 1));
		String s = nextLine();
		Stream<Object> fleet = Stream.of(s.substring(s.indexOf("[") + 1, s.indexOf("]")).split(",")).map(t -> {
			int pos = t.indexOf(":");
			return buildInternClassObject("ShipCategory", Integer.parseInt(t.substring(0, pos)), Integer.parseInt(t.substring(pos + 1)));
		});
		s = nextLine();
		int[] rowSums = Stream.of(s.substring(s.indexOf("[") + 1, s.indexOf("]")).split(",")).mapToInt(t -> Integer.parseInt(t)).toArray();
		s = nextLine();
		int[] colSums = Stream.of(s.substring(s.indexOf("[") + 1, s.indexOf("]")).split(",")).mapToInt(t -> Integer.parseInt(t)).toArray();
		s = nextLine();
		String[] toks = s.indexOf("[]") != -1 ? new String[0]
				: Stream.of(s.substring(s.indexOf("[") + 1, s.indexOf("]]") + 1).split("@|\\[|\\]|,")).filter(t -> t.length() > 0).toArray(String[]::new);
		Utilities.control(toks.length % 3 == 0, "Pb here " + Utilities.join(toks));
		Stream<Object> hints = IntStream.range(0, toks.length / 3)
				.mapToObj(i -> buildInternClassObject("Hint", toks[i * 3], Integer.parseInt(toks[i * 3 + 1]), Integer.parseInt(toks[i * 3 + 2])));
		imp().parameters.remove(1);
		imp().parameters.add(new SimpleEntry<>(id, "%05d"));
		setDataValues(fleet, rowSums, colSums, hints);
	}
}
