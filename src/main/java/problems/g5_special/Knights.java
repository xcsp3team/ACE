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

public class Knights implements ProblemAPI {

	int n; // order (board width)
	int nKnights;

	@Override
	public void model() {
		Var[] x = array("x", size(nKnights), dom(range(n * n)), "x[i] is the cell number of the board where is put the ith knight");

		forall(range(nKnights).range(nKnights), (i, j) -> {
			if (i + 1 < j && (i != 0 || j != nKnights - 1))
				different(x[i], x[j]);
		});
		slide(x, range(nKnights), i -> intension(knightAttack(x[i], x[(i + 1) % nKnights], n)));
	}
}
