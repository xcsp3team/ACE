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

class QueensPions implements ProblemAPI {
	int order, nQueens, nPions;

	@Override
	public void model() {
		Var[] q = array("q", size(nQueens), dom(range(order)));
		Var[] p = array("p", size(nPions), dom(range(order * order)));

		forall(range(nQueens), i -> forall(range(i + 1, nQueens), j -> conjunction(ne(q[i], q[j]), ne(dist(q[i], q[j]), dist(i, j)))));
		forall(range(nPions), i -> forall(range(i + 1, nPions), j -> conjunction(lt(dist(p[i], p[j]), nPions - 1), ne(p[i], p[j]))));

		if (modelVariant("mul"))
			forall(range(nQueens).range(nPions), (i, j) -> disjunction(ne(q[i], mod(p[j], order)), ne(div(p[j], order), i)));
	}
}
