/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.Arrays;
import java.util.stream.IntStream;

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.api.ProblemAPI;

import problems.BorderArray;

public class Shikaku implements ProblemAPI {

	int nRows, nCols;
	Room[] rooms;

	class Room {
		int row, col, value;
	}

	@Override
	public void model() {
		int nRooms = rooms.length;

		Var[] l = array("l", size(nRooms), dom(range(nCols + 1)), "l[i] is the position of the left border of the ith room");
		Var[] r = array("r", size(nRooms), dom(range(nCols + 1)), "r[i] is the position of the right border of the ith room");
		Var[] t = array("t", size(nRooms), dom(range(nRows + 1)), "t[i] is the position of the top border of the ith room");
		Var[] b = array("b", size(nRooms), dom(range(nRows + 1)), "b[i] is the position of the bottom border of the ith room");

		forall(range(nRooms), i -> lessEqual(l[i], rooms[i].col));
		forall(range(nRooms), i -> greaterThan(r[i], rooms[i].col));
		forall(range(nRooms), i -> lessEqual(t[i], rooms[i].row));
		forall(range(nRooms), i -> greaterThan(b[i], rooms[i].row));
		forall(range(nRooms), i -> equal(mul(sub(r[i], l[i]), sub(b[i], t[i])), rooms[i].value));
		forall(range(nRooms).range(nRooms), (i, j) -> {
			if (i < j) {
				int leftmost = rooms[i].col <= rooms[j].col ? i : j, rightmost = leftmost == i ? j : i;
				XNodeParent<IVar> p = le(r[leftmost], l[rightmost]);
				if (rooms[leftmost].row == rooms[rightmost].row)
					intension(p);
				else if (rooms[leftmost].row > rooms[rightmost].row)
					disjunction(p, ge(t[leftmost], b[rightmost]));
				else
					disjunction(p, le(b[leftmost], t[rightmost]));
			}
		}).note("rooms must not overlap");
	}

	@Override
	public void prettyDisplay(String[] values) {
		int nRooms = rooms.length;
		BorderArray ba = new BorderArray(nRows + 1, nCols + 1);
		IntStream.range(0, nRooms).forEach(i -> ba.writeBorder(values[i], values[i + nRooms], values[i + 2 * nRooms], values[i + 3 * nRooms]));
		Arrays.stream(rooms).forEach(r -> ba.writeValue(r.row, r.col, r.value));
		System.out.println(ba.toString());
	}
}
