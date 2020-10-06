/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g1_single;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.hard.extension.CtrExtensionSmart;
import constraints.hard.extension.structures.SmartTuple;
import problem.Problem;
import variables.Variable;

public class Solitaire implements ProblemAPI {

	private boolean isValidPosition(int i, int j) {
		return !((i < 2 && j < 2) || (i < 2 && j > 4) || (i > 4 && j < 2) || (i > 4 && j > 4));
	}

	private boolean isValidPosition(int v) {
		return 0 <= v && v < 49 && isValidPosition(v / 7, v % 7);
	}

	private int[] validPositions() {
		return IntStream.range(0, 49).filter(v -> isValidPosition(v)).toArray();
	}

	private boolean onSameRow(int v1, int v2, int v3) {
		return v1 / 7 == v2 / 7 && v2 / 7 == v3 / 7;
	}

	private int[] l2r() {
		return IntStream.of(validPositions()).filter(v -> isValidPosition(v + 1) && isValidPosition(v + 2) && onSameRow(v, v + 1, v + 2)).toArray();
	}

	private int[] r2l() {
		return IntStream.of(validPositions()).filter(v -> isValidPosition(v - 1) && isValidPosition(v - 2) && onSameRow(v, v - 1, v - 2)).toArray();
	}

	private int[] t2b() {
		return IntStream.of(validPositions()).filter(v -> isValidPosition(v + 7) && isValidPosition(v + 14)).toArray();
	}

	private int[] b2t() {
		return IntStream.of(validPositions()).filter(v -> isValidPosition(v - 7) && isValidPosition(v - 14)).toArray();
	}

	private SmartTuple[] smartTuples(Var m1, Var[][] x1, Var[][] x2) {
		List<SmartTuple> list = new ArrayList<>();
		int cnt = 0;
		for (int v : l2r()) {
			List<XNodeParent<? extends IVar>> restrictions = new ArrayList<>();
			restrictions.add(eq(m1, cnt++));
			for (int w : validPositions())
				if (w == v || w == v + 1) {
					restrictions.add(eq(x1[w / 7][w % 7], 1));
					restrictions.add(eq(x2[w / 7][w % 7], 0));
				} else if (w == v + 2) {
					restrictions.add(eq(x1[w / 7][w % 7], 0));
					restrictions.add(eq(x2[w / 7][w % 7], 1));
				} else
					restrictions.add(eq(x1[w / 7][w % 7], x2[w / 7][w % 7]));
			list.add(new SmartTuple(restrictions));
		}
		for (int v : r2l()) {
			List<XNodeParent<? extends IVar>> restrictions = new ArrayList<>();
			restrictions.add(eq(m1, cnt++));
			for (int w : validPositions())
				if (w == v || w == v - 1) {
					restrictions.add(eq(x1[w / 7][w % 7], 1));
					restrictions.add(eq(x2[w / 7][w % 7], 0));
				} else if (w == v - 2) {
					restrictions.add(eq(x1[w / 7][w % 7], 0));
					restrictions.add(eq(x2[w / 7][w % 7], 1));
				} else
					restrictions.add(eq(x1[w / 7][w % 7], x2[w / 7][w % 7]));
			list.add(new SmartTuple(restrictions));
		}
		for (int v : t2b()) {
			List<XNodeParent<? extends IVar>> restrictions = new ArrayList<>();
			restrictions.add(eq(m1, cnt++));
			for (int w : validPositions())
				if (w == v || w == v + 7) {
					restrictions.add(eq(x1[w / 7][w % 7], 1));
					restrictions.add(eq(x2[w / 7][w % 7], 0));
				} else if (w == v + 14) {
					restrictions.add(eq(x1[w / 7][w % 7], 0));
					restrictions.add(eq(x2[w / 7][w % 7], 1));
				} else
					restrictions.add(eq(x1[w / 7][w % 7], x2[w / 7][w % 7]));
			list.add(new SmartTuple(restrictions));
		}
		for (int v : b2t()) {
			List<XNodeParent<? extends IVar>> restrictions = new ArrayList<>();
			restrictions.add(eq(m1, cnt++));
			for (int w : validPositions())
				if (w == v || w == v - 7) {
					restrictions.add(eq(x1[w / 7][w % 7], 1));
					restrictions.add(eq(x2[w / 7][w % 7], 0));
				} else if (w == v - 14) {
					restrictions.add(eq(x1[w / 7][w % 7], 0));
					restrictions.add(eq(x2[w / 7][w % 7], 1));
				} else
					restrictions.add(eq(x1[w / 7][w % 7], x2[w / 7][w % 7]));
			list.add(new SmartTuple(restrictions));
		}
		return list.toArray(new SmartTuple[0]);
	}

	@Override
	public void model() {
		int nMoves = 31; // 31
		Var[][][] x = array("x", size(nMoves + 1, 7, 7), (t, i, j) -> isValidPosition(i, j) ? dom(0, 1) : null,
				"x[t][i][j] is the value of the board at time t and row i and col j");
		Var[] m = array("m", size(nMoves), dom(range(76)), "m[t] is the move at time t");

		instantiation(vars(x[0]), vals(repeat(1, 16), 0, repeat(1, 16)));
		equal(m[0], 8);
		instantiation(vars(x[31]), vals(repeat(0, 16), 1, repeat(0, 16)));

		forall(range(nMoves), t -> ((Problem) imp())
				.addCtr(new CtrExtensionSmart(((Problem) imp()), (Variable[]) vars(m[t], x[t], x[t + 1]), smartTuples(m[t], x[t], x[t + 1]))));

		// ((Problem) imp()).priorityVars = (Variable[]) m;
	}
}
