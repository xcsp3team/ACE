/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g5_special;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

/*
 * "Queens-Knights problem." + "\nAs defined by [Boussemart, Hemery, Lecoutre and Sais, Boosting systematic search by weighting constraints, 2004]." +
 * "\nOn a chessboard of a specified size, a specified number of queens and knigths must be placed."
 */
// 9 4 32 vs 9 4 33 ; 10 4 72 vs 10 4 73
public class QueensKnights implements ProblemAPI {
	int n;
	int nQueens;
	int nKnights;

	@Override
	public void model() {
		Var[] q = array("q", size(nQueens), dom(range(n)));
		Var[] k = array("k", size(nKnights), dom(range(n * n)));

		forall(range(nQueens), i -> forall(range(i + 1, nQueens), j -> conjunction(ne(q[i], q[j]), ne(dist(i, j), dist(q[i], q[j])))));
		forall(range(nKnights), i -> intension(knightAttack(k[i], k[(i + 1) % nKnights], n)));
		forall(range(nKnights).range(nKnights), (i, j) -> {
			if (j > i + 1 && (i != 0 || j != nKnights - 1))
				different(k[i], k[j]);
		});
		if (modelVariant("mul"))
			forall(range(nQueens).range(nKnights), (i, j) -> disjunction(ne(q[i], mod(k[j], n)), ne(i, div(k[j], n))));
	}
}
