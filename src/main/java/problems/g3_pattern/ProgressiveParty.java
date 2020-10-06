/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class ProgressiveParty implements ProblemAPI {
	int nPeriods;
	Boat[] boats;

	class Boat {
		int capacity, crewSize;
	}

	@Override
	public void model() {
		int nBoats = boats.length;
		int[] crewSizes = Stream.of(boats).mapToInt(b -> b.crewSize).toArray();

		Var[] h = array("h", size(nBoats), dom(0, 1), "h[b] indicates if the boat b is a host boat");
		Var[][] s = array("s", size(nBoats, nPeriods), dom(range(nBoats)), "s[b][p] is the scheduled (visited) boat by the crew of boat b at period p");
		Var[][][] g = array("g", size(nBoats, nPeriods, nBoats), dom(0, 1), "g[b1][p][b2] is 1 if s[b1][p] = b2");

		forall(range(nBoats).range(nPeriods), (b, p) -> equivalence(eq(s[b][p], b), h[b])).note("identifying host boats (when receiving)");
		forall(range(nBoats).range(nBoats).range(nPeriods), (b1, b2, p) -> {
			if (b1 != b2)
				implication(eq(s[b1][p], b2), h[b2]);
		}).note("identifying host boats (when visiting)");

		forall(range(nBoats).range(nPeriods), (b, p) -> channel(g[b][p], s[b][p])).note("channeling variables from arrays s and g");
		forall(range(nBoats).range(nPeriods), (b, p) -> sum(select(g, (i, j, k) -> j == p && k == b), crewSizes, LE, boats[b].capacity))
				.note("boat capacities must be respected");
		forall(range(nBoats), b -> allDifferent(s[b], exceptValue(b))).note("a guest boat cannot revisit a host");

		forall(range(nBoats).range(nBoats), (b1, b2) -> {
			if (b1 < b2)
				sum(treesFrom(range(nPeriods), p -> eq(s[b1][p], s[b2][p])), LE, 2);
		}).note("guest crews cannot meet more than once");

		minimize(SUM, h).note("minimizing the number of host boats");
	}
}
