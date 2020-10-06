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
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Table;
import org.xcsp.common.structures.Transitions;
import org.xcsp.modeler.api.ProblemAPI;

// pb 014 on CSPLib
public class SolitaireBattleship implements ProblemAPI {

	ShipCategory[] fleet;
	int[] rowSums;
	int[] colSums;
	Hint[] hints;

	class ShipCategory {
		int size, cnt;
	}

	class Hint {
		String type;
		int row, col;
	}

	private Automaton automataForShipsOnLine(boolean hor) {
		int[] pos = Stream.of(fleet).mapToInt(s -> s.size).toArray(), neg = Stream.of(fleet).mapToInt(s -> -s.size).toArray();
		int[] t1 = hor ? neg : pos, t2 = hor ? pos : neg;
		Transitions transitions = transitions().add("q0", 0, "q0").add("q0", t1, "qq").add("qq", 0, "q0");
		for (int i : t2) {
			int absi = Math.abs(i);
			transitions.add("q0", i, "q" + absi + "x" + 1);
			IntStream.range(1, absi).forEach(j -> transitions.add("q" + absi + "x" + j, i, "q" + absi + "x" + (j + 1)));
			transitions.add("q" + absi + "x" + absi, 0, "q0");
		}
		return automaton("q0", transitions, "q0");
	}

	@Override
	public void model() {
		int[] sizes = valuesFrom(fleet, ship -> ship.size), occurrences = valuesFrom(fleet, ship -> ship.size * ship.cnt);
		int[] pos = sizes, neg = valuesFrom(pos, v -> -v);
		int[] values = valuesIn(pos, neg); // IntStream.concat(IntStream.of(pos), IntStream.of(neg)).toArray();
		int n = colSums.length, nSizes = sizes.length, maxOccurrence = maxOf(occurrences);

		Var[][] s = array("s", size(n + 2, n + 2), dom(0, 1), "s[i][j] is 1 iff the cell at row i and col j is occupied by a ship segment");
		Var[][] t = array("t", size(n + 2, n + 2), dom(0, values),
				"t[i][j] is 0 iff the cell at row i and col j is unoccupied, the type (size) of the ship fragment otherwise, when positive, the ship is put horizontally, when negative, the ship is put vertically");
		Var[] cp = array("cp", size(pos.length), dom(range(maxOccurrence + 1)), "cp[i] is the number of positive ship segments of type i");
		Var[] cn = array("cn", size(neg.length), i -> neg[i] == -1 ? dom(0) : dom(range(maxOccurrence + 1)),
				"cn[i] is the number of negative ship segments of type i");

		block(() -> {
			sum(s[0], EQ, 0);
			sum(s[n + 1], EQ, 0);
			sum(columnOf(s, 0), EQ, 0);
			sum(columnOf(s, n + 1), EQ, 0);
		}).note("no ship on borders");
		block(() -> {
			forall(range(n), i -> sum(s[i + 1], EQ, rowSums[i]));
			forall(range(n), j -> sum(columnOf(s, j + 1), EQ, colSums[j]));
		}).note("respecting the specified row and column tallies");

		Table table = table().add(0, STAR, STAR, STAR, STAR).add(1, 0, 0, 0, 0);
		forall(rangeClosed(1, n).rangeClosed(1, n),
				(i, j) -> extension(vars(s[i][j], s[i - 1][j - 1], s[i - 1][j + 1], s[i + 1][j + 1], s[i + 1][j - 1]), table))
						.note("being careful about cells on diagonals");
		forall(range(n + 2).range(n + 2), (i, j) -> equivalence(eq(s[i][j], 1), ne(t[i][j], 0))).tag(CHANNELING);

		block(() -> {
			Var[] scp = select(t, (i, j) -> 1 <= i && i <= n && 1 <= j && j <= n);
			cardinality(scp, pos, occurExactly(cp)); // forall(range(nSizes), i -> count(scp, pos[i], EQ, cp[i]));
			cardinality(scp, neg, occurExactly(cn)); // forall(range(nSizes), i -> count(scp, neg[i], EQ, cn[i]));
			forall(range(nSizes), i -> equal(add(cp[i], cn[i]), occurrences[i]));
		}).note("ensuring the right number of occurrences of ship segments of each type");

		block(() -> {
			Automaton ah = automataForShipsOnLine(true), av = automataForShipsOnLine(false);
			forall(rangeClosed(1, n), i -> regular(t[i], ah));
			forall(rangeClosed(1, n), j -> regular(columnOf(t, j), av));
		}).note("ensuring connexity of ship segments");

		if (hints != null)
			forall(range(hints.length), h -> {
				Hint hint = hints[h];
				int i = hint.row, j = hint.col;
				char c = hint.type.charAt(0);
				if (c == 'w')
					equal(s[i][j], 0);
				else if (c == 'c' || c == 'l' || c == 'r' || c == 't' || c == 'b') {
					equal(s[i][j], 1);
					equal(s[i - 1][j], c == 'b' ? 1 : 0);
					equal(s[i + 1][j], c == 't' ? 1 : 0);
					equal(s[i][j - 1], c == 'r' ? 1 : 0);
					equal(s[i][j + 1], c == 'l' ? 1 : 0);
				} else if (c == 'm') {
					equal(s[i][j], 1);
					intension(not(in(t[i][j], set(-2, -1, 0, 1, 2))));
					extension(vars(s[i - 1][j], s[i + 1][j], s[i][j - 1], s[i][j + 1]), table().add(0, 0, 1, 1).add(1, 1, 0, 0));
				}
			}).tag(CLUES);

	}
}

// Var[][][] r = array("r", size(n + 2, n + 2, 4), (i, j, k) -> i == 0 || i == n + 1 || j == 0 || j == n + 1 ? dom(0) : dom(0, 1));
// forall(range(1, n).range(1, n), (i, j) -> intension(iff(eq(r[i][j][0], 1), and(eq(s[i][j], 1), eq(s[i][j + 1], 1)))));
// forall(range(1, n).range(1, n).range(4), (i, j, k) -> {
// if (j + k <= n)
// intension(iff(eq(r[i][j][k], 1), and(eq(r[i][j][k - 1], 1), eq(s[i][j + k + 1], 1))));
// });

// cardinality(select(t, (i, j) -> 1 <= i && i <= n && 1 <= j && j <= n), sizes, occurrences(occurrences));
