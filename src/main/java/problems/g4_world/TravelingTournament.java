/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Table;
import org.xcsp.common.structures.Transitions;
import org.xcsp.modeler.api.ProblemAPI;

public class TravelingTournament implements ProblemAPI {

	int[][] distances;

	private Table tableEnd(int i) {
		Table table = table().add(1, STAR, 0); // note that when playing at home (whatever the opponent, travel distance is 0)
		return table.addFrom(range(distances.length), j -> j != i ? tuple(0, j, distances[i][j]) : null);
	}

	private Table tableOther(int i) {
		int nTeams = distances.length;
		Table table = table().add(1, 1, STAR, STAR, 0);
		table.addFrom(range(nTeams), j -> j != i ? tuple(0, 1, j, STAR, distances[i][j]) : null);
		table.addFrom(range(nTeams), j -> j != i ? tuple(1, 0, STAR, j, distances[i][j]) : null);
		return table.addFrom(range(nTeams).range(nTeams), (j1, j2) -> j1 != i && j2 != i && j1 != j2 ? tuple(0, 0, j1, j2, distances[j1][j2]) : null);
	}

	private Automaton buildAutomaton() {
		Transitions transitions = transitions("(q,0,q01)(q,1,q11)(q01,0,q02)(q01,1,q11)(q11,0,q01)(q11,1,q12)(q02,1,q11)(q12,0,q01)");
		if (modelVariant("a2"))
			return automaton("q", transitions, finalStates("q01", "q02", "q11", "q12"));
		transitions = transitions(transitions + "(q02,0,q03)(q12,1,q13)(q03,1,q11)(q13,0,q01)");
		return automaton("q", transitions, finalStates("q01", "q02", "q03", "q11", "q12", "q13"));
	}

	@Override
	public void model() {
		int nTeams = distances.length, nRounds = nTeams * 2 - 2;
		Utilities.control(nTeams % 2 == 0, "An even number of teams is expected");

		Var[][] o = array("o", size(nTeams, nRounds), dom(range(nTeams)), "o[i][k] is the opponent (team) of the ith team  at the kth round");
		Var[][] h = array("h", size(nTeams, nRounds), dom(0, 1), "h[i][k] is 1 iff the ith team plays at home at the kth round");
		Var[][] a = array("a", size(nTeams, nRounds), dom(0, 1), "a[i][k] is 0 iff the ith team plays away at the kth round");
		Var[][] t = array("t", size(nTeams, nRounds + 1), dom(distances),
				"t[i][k] is the travelled distance by the ith team at the kth round. An additional round is considered for returning at home.");

		forall(range(nTeams), i -> cardinality(o[i], range(nTeams).select(j -> j != i), CLOSED, occursEachExactly(2)))
				.note("each team must play exactly two times against each other team");
		forall(range(nTeams).range(nRounds), (i, k) -> element(columnOf(o, k), at(o[i][k]), takingValue(i)))
				.note("ensuring symmetry of games: if team i plays against j at round k, then team j plays against i at round k");

		forall(range(nTeams).range(nRounds), (i, k) -> equal(h[i][k], not(a[i][k]))).note("playing home at round k iff not playing away at round k");
		forall(range(nTeams).range(nRounds), (i, k) -> element(columnOf(h, k), at(o[i][k]), takingValue(a[i][k]))).note("channeling the three arrays");
		forall(range(nTeams).range(nRounds).range(nRounds), (i, k1, k2) -> {
			if (k1 + 1 < k2)
				implication(eq(o[i][k1], o[i][k2]), ne(h[i][k1], h[i][k2]));
		}).note("playing against the same team must be done once at home and once away");

		forall(range(nRounds), k -> allDifferent(columnOf(o, k))).tag(REDUNDANT_CONSTRAINTS).note("at each round, opponents are all different");
		lessThan(o[0][0], o[0][nRounds - 1]).tag(SYMMETRY_BREAKING);

		Automaton automaton = buildAutomaton();
		forall(range(nTeams), i -> regular(h[i], automaton))
				.note("at most " + (modelVariant("a2") ? 2 : 3) + " consecutive games at home, or consecutive games away");

		forall(range(nTeams), i -> extension(vars(h[i][0], o[i][0], t[i][0]), tableEnd(i))).note("handling travelling for the first game");

		forall(range(nTeams), i -> extension(vars(h[i][nRounds - 1], o[i][nRounds - 1], t[i][nRounds]), tableEnd(i)))
				.note("handling travelling for the last game");
		forall(range(nTeams).range(nRounds - 1), (i, k) -> extension(vars(h[i][k], h[i][k + 1], o[i][k], o[i][k + 1], t[i][k + 1]), tableOther(i)))
				.note("handling travelling for two successive games");

		minimize(SUM, t).note("minimizing summed up travelled distance");
	}
}
// Var[][] o = array("o", size(nTeams, nRounds), dom(range(-nTeams, nTeams)), // alternative model ?

// for (int j1 = 0; j1 < distances.length; j1++)
// for (int j2 = 0; j2 < distances.length; j2++)
// if (j1 != i && j2 != i && j1 != j2)
// table.add(0, 0, j1, j2, distances[j1][j2]);