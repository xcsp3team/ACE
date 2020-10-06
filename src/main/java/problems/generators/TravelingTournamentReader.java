/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.TravelingTournament;

public class TravelingTournamentReader extends TravelingTournament implements ReaderTxt {
	void data() {
		int[] t = Utilities.splitToInts(nextLine().trim());
		int[][] distances = range(t.length).range(t.length).map((i, j) -> i == 0 ? t[j] : nextInt());
		setDataValues(distances);
	}
}
