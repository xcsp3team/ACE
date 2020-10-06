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
import problems.g4_world.League;

public class LeagueReaderZ extends League implements ReaderDzn {

	void data() {
		int leagueSize = nextInt();
		int nPlayers = nextInt();
		int[] playerRankings = nextInt1D();
		int[] playerCountries = nextInt1D();
		Stream<Object> players = IntStream.range(0, nPlayers).mapToObj(i -> buildInternClassObject("Player", playerRankings[i], playerCountries[i]));
		setDataValues(leagueSize, players);
	}
}
