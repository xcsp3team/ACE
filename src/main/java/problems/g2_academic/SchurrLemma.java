/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

/*
 * "Schurr's lemma problem." +
 * "\nOne variant corresponds to the one proposed by [Bessiere Meseguer Freuder Larrosa, On forward checking for non-binary constraint satisfaction, 2002]." +
 * " \nSee http://4c.ucc.ie/~tw/csplib/prob/prob015/index.html"
 */
public class SchurrLemma implements ProblemAPI {
	int nBalls, nBoxes;

	@Override
	public void model() {
		Var[] x = array("x", size(nBalls), dom(range(nBoxes)), "x[i] is the box where the ith ball is put");

		forall(range(nBalls).range(nBalls).range(nBalls), (i, j, k) -> {
			if (i < j && j < k && i + 1 + j + 1 == k + 1)
				if (!modelVariant("mod"))
					notAllEqual(x[i], x[j], x[k]);
				else
					allDifferent(x[i], x[j], x[k]);
		});
	}
}
