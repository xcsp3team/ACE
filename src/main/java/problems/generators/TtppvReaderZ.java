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
import problems.g4_world.TravelingTournamentWithPredefinedVenues;

public class TtppvReaderZ extends TravelingTournamentWithPredefinedVenues implements ReaderDzn {

	void data() {
		int nTeams = nextInt();
		int[][] pv = nextInt2D();
		Stream.of(pv).forEach(t -> IntStream.range(0, t.length).filter(j -> t[j] == 2).forEach(j -> t[j] = 0));
		setDataValues(nTeams, (Object) pv);
	}
}
