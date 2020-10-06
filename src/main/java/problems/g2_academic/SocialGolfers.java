/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Range;
import org.xcsp.modeler.api.ProblemAPI;

public class SocialGolfers implements ProblemAPI {
	int nGroups, groupSize, nWeeks;

	private Var[][] project3(Var[][][] m) {
		return IntStream.range(0, m[0][0].length).mapToObj(i -> select(m, (w, g, p) -> p == i)).toArray(Var[][]::new);
	}

	@Override
	public void model() {
		Range allGroups = range(nGroups);
		int nPlayers = nGroups * groupSize;

		if (modelVariant("")) {
			Var[][] g = array("g", size(nWeeks, nPlayers), dom(allGroups), "g[w][p] is the group admitting on week w the player p");

			forall(range(nWeeks).range(nWeeks).range(nPlayers).range(nPlayers), (w1, w2, p1, p2) -> {
				if (w1 < w2 && p1 < p2)
					disjunction(ne(g[w1][p1], g[w1][p2]), ne(g[w2][p1], g[w2][p2]));
			}).note("ensuring that two players don't meet more than one time"); // to be replaced by allDistant-list in a future model ?
			forall(range(nWeeks), w -> cardinality(g[w], allGroups, occursEachExactly(groupSize))).note("respecting the size of the groups");

			block(() -> {
				lexMatrix(g, INCREASING);
				instantiation(g[0], takingValues(range(nPlayers).map(p -> p / groupSize)));
				forall(range(groupSize), k -> instantiation(select(columnOf(g, k), w -> w > 0), takingValue(k)));
			}).tag(SYMMETRY_BREAKING);
		}
		if (modelVariant("01")) {
			Var[][][] x = array("x", size(nWeeks, nGroups, nPlayers), dom(0, 1), "x[w][g][p] is 1 iff on week w the group g admits the player p");
			Var[][][] tw = array("tw", size(nPlayers, nPlayers, nWeeks), (p1, p2, w) -> p1 < p2 ? dom(0, 1) : null,
					"tw[p1][p2][w] is 1 iff players p1 and p2 play together on week w");
			Var[][][][] twg = array("twg", size(nPlayers, nPlayers, nWeeks, nGroups), (p1, p2, w, g) -> p1 < p2 ? dom(0, 1) : null,
					"twg[p1][p2][w][g] is 1 iff players p1 and p2 play together on week w in group g");

			forall(range(nWeeks).range(nPlayers), (w, p) -> sum(select(x, (i, j, k) -> i == w && k == p), EQ, 1))
					.note("each week, each player plays exactly once");
			forall(range(nWeeks).range(nGroups), (w, g) -> sum(x[w][g], EQ, groupSize))
					.note("each week, each group contains exactly the right number of players");
			forall(range(nPlayers), p1 -> forall(range(p1 + 1, nPlayers), p2 -> sum(tw[p1][p2], LE, 1))).note("two players cannot meet twice");
			forall(range(nPlayers), p1 -> forall(range(p1 + 1, nPlayers).range(nWeeks), (p2, w) -> sum(twg[p1][p2][w], EQ, tw[p1][p2][w])))
					.note("deciding when two players play together");

			forall(range(nWeeks).range(nGroups).range(nPlayers).range(nPlayers), (w, g, p1, p2) -> {
				if (p1 < p2)
					equal(mul(x[w][g][p1], x[w][g][p2]), twg[p1][p2][w][g]);
			}).note("deciding when two players play in the same group");

			block(() -> {
				forall(range(nWeeks), w -> strictlyDecreasing(x[w])).note("each week, groups are strictly ordered");
				strictlyDecreasing(eliminateDim2(x, 0)).note("weeks are strictly ordered (it suffices to consider the first group)");
				strictlyDecreasing(project3(x)).note("golfers are strictly ordered");
			}).tag(SYMMETRY_BREAKING);
			// group(range(nWeeks - 1), w -> lex(sch[w][0], sch[w + 1][0], GT));
			// group(range(nPlayers - 1), p -> lex(select(sch, (i, j, k) -> k == p), select(sch, (i, j, k) -> k == p + 1), GT));

			// ((Problem) imp()).undisplay("tw", "tgw");
		}
	}
}

// forall(range(groupSize), k -> instantiation(select(x, (w, p) -> w > 0 && p == k), k));
