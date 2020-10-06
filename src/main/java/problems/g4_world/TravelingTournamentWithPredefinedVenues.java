/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

public class TravelingTournamentWithPredefinedVenues implements ProblemAPI {
	int nTeams;
	int[][] predefinedVenues;

	@NotData
	private String t = "(q,0,q01)(q,1,q11)(q01,0,q02)(q01,1,q11)(q11,0,q01)(q11,1,q12)(q02,1,q11)(q12,0,q01)";

	@NotData
	private Automaton aut2 = automaton("q", t, "q01", "q02", "q11", "q12");

	@NotData
	private Automaton aut3 = automaton("q", t + "(q02,0,q03)(q12,1,q13)(q03,1,q11)(q13,0,q01)", "q01", "q02", "q03", "q11", "q12", "q13");

	private int circDistance(int i, int j) {
		return Math.min(Math.abs(i - j), nTeams - Math.abs(i - j));
	}

	private Table tableFirstOrLastGame(int i) {
		Table table = table().add(1, STAR, 0); // when playing at home (whatever the opponent, travel distance is 0)
		return table.add(IntStream.range(0, nTeams).filter(j -> j != i).mapToObj(j -> tuple(0, j, circDistance(i, j))));
	}

	private Table tableForInternalGame(int i) {
		Table table = table().add(1, 1, STAR, STAR, 0);
		table.add(IntStream.range(0, nTeams).filter(j -> j != i).mapToObj(j -> tuple(0, 1, j, STAR, circDistance(j, i))));
		table.add(IntStream.range(0, nTeams).filter(j -> j != i).mapToObj(j -> tuple(1, 0, STAR, j, circDistance(i, j))));
		for (int j1 = 0; j1 < nTeams; j1++)
			for (int j2 = 0; j2 < nTeams; j2++)
				if (j1 != i && j2 != i && j1 != j2)
					table.add(0, 0, j1, j2, circDistance(j1, j2));
		return table;
	}

	@Override
	public void model() {
		Utilities.control(nTeams % 2 == 0, "an even number of teams is expected");
		int nRounds = nTeams - 1;

		Var[][] o = array("o", size(nTeams, nRounds), dom(range(nTeams)), "o[i][k] is the opponent (team) of the ith team  at the kth round");
		Var[][] h = array("h", size(nTeams, nRounds), dom(0, 1), "h[i][k] is 1 iff the ith team plays at home at the kth round");
		Var[][] t = array("t", size(nTeams, nRounds + 1), dom(range(nTeams / 2 + 1)),
				"t[i][k] is the travelled distance by the ith team at the kth round. An additional round is considered for returning at home.");

		forall(range(nTeams).range(nRounds), (i, k) -> different(o[i][k], i)).note("a team cannot play against itself");
		forall(range(nTeams).range(nRounds), (i, k) -> element(predefinedVenues[i], o[i][k], h[i][k])).note("ensuring predefined venues");
		forall(range(nTeams).range(nRounds), (i, k) -> element(columnOf(o, k), o[i][k], i))
				.note("ensuring symmetry of games: if team i plays against j, then team j plays against i");
		forall(range(nTeams), i -> allDifferent(o[i])).note("each team plays once against all other teams");

		forall(range(nTeams), i -> regular(h[i], modelVariant("a2") ? aut2 : aut3))
				.note("at most " + (modelVariant("a2") ? 2 : 3) + " consecutive games at home, or consecutive games away");

		forall(range(nTeams), i -> extension(vars(h[i][0], o[i][0], t[i][0]), tableFirstOrLastGame(i))).note("handling travelling for the first game");
		forall(range(nTeams), i -> extension(vars(h[i][nRounds - 1], o[i][nRounds - 1], t[i][nRounds]), tableFirstOrLastGame(i)))
				.note("handling travelling for the last game");
		forall(range(nTeams).range(nRounds - 1), (i, k) -> extension(vars(h[i][k], h[i][k + 1], o[i][k], o[i][k + 1], t[i][k + 1]), tableForInternalGame(i)))
				.note("handling travelling for two successive games");

		forall(range(nRounds), k -> allDifferent(columnOf(o, k))).tag(REDUNDANT_CONSTRAINTS).note("at each round, opponents are all different");
		lessThan(o[0][0], o[0][nRounds - 1]).tag(SYMMETRY_BREAKING);

		minimize(SUM, t).note("minimizing summed up travelled distance");
	}
}