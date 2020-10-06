/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

public class League implements ProblemAPI {
	int leagueSize;
	Player[] players;

	class Player {
		int ranking, country;
	}

	@Override
	public void model() {
		int nPlayers = players.length;
		int nLeagues = nPlayers / leagueSize + (nPlayers % leagueSize != 0 ? 1 : 0);
		int nFullLeagues = nPlayers % leagueSize == 0 ? nLeagues : nLeagues - (leagueSize - nPlayers % leagueSize);
		int[] playerRankings = Stream.of(players).mapToInt(p -> p.ranking).toArray();
		int[] playerCountries = Stream.of(players).mapToInt(p -> p.country).toArray();
		int[] allRankings = singleValuesIn(playerRankings);
		int[] allCountries = singleValuesIn(playerCountries);

		Var[][] p = array("p", size(nLeagues, leagueSize), (i, j) -> i < nFullLeagues || j < leagueSize - 1 ? dom(range(nPlayers)) : null,
				"p[i][j] is the jth player of the ith league");
		Var[][] r = array("r", size(nLeagues, leagueSize), (i, j) -> i < nFullLeagues || j < leagueSize - 1 ? dom(playerRankings) : null,
				"r[i][j] is the ranking of the jth player of the ith league");
		Var[] l = array("l", size(nLeagues), i -> dom(playerRankings), "l[i] is the lowest ranking of a player of the ith league");
		Var[] h = array("h", size(nLeagues), i -> dom(playerRankings), "h[i] is the highest ranking of a player of the ith league");
		Var[] d = array("d", size(nLeagues), i -> dom(0, allRankings),
				"d[i] is the difference between the highest and lowest rankings of players of the ith league");

		Var[] nc = array("nc", size(nLeagues), i -> dom(range(1 + Math.min(allCountries.length, i < nFullLeagues ? leagueSize : leagueSize - 1))),
				"nc[i] is the number of countries for players of the ith league");

		allDifferent(p);
		forall(range(nLeagues), i -> minimum(r[i], l[i]));
		forall(range(nLeagues), i -> maximum(r[i], h[i]));
		forall(range(nLeagues), i -> equal(d[i], sub(h[i], l[i])));

		// symmetry breaking lex
		// lexMatrix(lp);

		if (modelVariant("")) {
			Var[][] c = array("c", size(nLeagues, leagueSize), (i, j) -> i < nFullLeagues || j < leagueSize - 1 ? dom(playerCountries) : null,
					"c[i][j] is the country of the jth player of the ith league");

			Table table = table().addFrom(range(nPlayers), i -> tuple(i, playerRankings[i], playerCountries[i]));
			forall(range(nLeagues).range(leagueSize), (i, j) -> {
				if (i < nFullLeagues || j < leagueSize - 1)
					extension(vars(p[i][j], r[i][j], c[i][j]), table);
			});
			forall(range(nLeagues), i -> nValues(c[i], EQ, nc[i]));
		}
		// TODO PB with this model : to be fixed
		// if (modelVariant("01")) {
		// int nCountries = allCountries.length;
		// Var[][] c = array("c", size(nLeagues, nCountries), dom(0, 1), "c[i][k] is 1 if at least one player of the ith league is from country k");
		//
		// Table table = table().addFrom(range(nPlayers),
		// i -> valuesFrom(range(2 + nCountries), j -> j == 0 ? i : j == 1 ? playerRankings[i] : j - 2 + 1 == playerCountries[i] ? 1 : STAR));
		// forall(range(nLeagues).range(leagueSize), (i, j) -> {
		// if (i < nFullLeagues || j < leagueSize - 1)
		// extension(vars(p[i][j], r[i][j], c[i]), table);
		// });
		// forall(range(nLeagues).range(leagueSize).range(nCountries).range(nPlayers), (i, j, k, m) -> {
		// if (i < nFullLeagues || j < leagueSize - 1) {
		// if (playerCountries[m] == k + 1)
		// implication(eq(c[i][k], 0), ne(p[i][j], m));
		// }
		// });
		// forall(range(nLeagues), i -> sum(c[i], EQ, nc[i]));
		// }

		minimize(SUM, vars(d, nc), vals(repeat(100, nLeagues), repeat(-1, nLeagues)));
	}
}