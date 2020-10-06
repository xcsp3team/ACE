/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

// proposed by becool team (and revised by C. Lecoutre)
public class Eternity implements ProblemAPI {
	int n, m;
	int[][] pieces;

	private Table piecesTable() {
		Table table = table();
		forall(range(n * m).range(4), (i, r) -> table.add(i, pieces[i][r % 4], pieces[i][(r + 1) % 4], pieces[i][(r + 2) % 4], pieces[i][(r + 3) % 4]));
		return table;
	}

	@Override
	public void model() {
		Utilities.control(n * m == pieces.length, "badly formed data");
		int maxValue = maxOf(valuesIn(pieces)); // max possible value on pieces

		Var[][] id = array("id", size(n, m), dom(range(n * m)), "id[i][j] is the id of the piece at row i and column j");
		Var[][] top = array("top", size(n, m), dom(range(maxValue + 1)), "top[i][j] is the value at the top of the piece put at row i and column j");
		Var[][] left = array("left", size(n, m), dom(range(maxValue + 1)), "left[i][j] is the value at the left of the piece put at row i and column j");
		Var[] bot = array("bot", size(m), dom(range(maxValue + 1)), "bot[j] is the value at the bottom of the piece put at the bottommost row and column j");
		Var[] right = array("right", size(n), dom(range(maxValue + 1)),
				"right[i] is the value at the right of the piece put at the row i and the rightmost column");

		allDifferent(id).note("all pieces must be placed (only once)");

		Table table = piecesTable();
		forall(range(n).range(m),
				(i, j) -> extension(vars(id[i][j], top[i][j], j < m - 1 ? left[i][j + 1] : right[j], i < n - 1 ? top[i + 1][j] : bot[j], left[i][j]), table))
						.note("all pieces must be valid (i.e., must correspond to those given initially, possibly after considering some rotation)");
		// block(() -> {
		// instantiation(columnOf(left, 0), 0);
		// instantiation(right, 0);
		// instantiation(top[0], 0);
		// instantiation(bot, 0);
		//
		// // forall(range(n), i -> equal(left[i][0], 0));
		// // forall(range(n), i -> equal(right[i], 0));
		// // forall(range(m), j -> equal(top[0][j], 0));
		// // forall(range(m), j -> equal(bot[j], 0));
		// }).note("put special value 0 on borders");
		// TODO replace by constraint instantiation above

		instantiation(vars(columnOf(left, 0), right, top[0], bot), 0).note("put special value 0 on borders");

	}
}

// int maxValue = Stream.of(pieces).map(t -> IntStream.of(t)).flatMapToInt(i -> i).max().getAsInt(); // max possible value on pieces

// block(() -> {
// forall(range(n), i -> equal(left[i][0], 0));
// forall(range(n), i -> equal(right[i], 0));
// forall(range(m), j -> equal(top[0][j], 0));
// forall(range(m), j -> equal(bot[j], 0));
// }).note("put special value 0 on borders");