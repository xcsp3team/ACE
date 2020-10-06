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

/* This problem corresponds to the one described in [Puget, AAAI'98] */
public class PathologicalAllDifferent implements ProblemAPI {
	int n;

	@Override
	public void model() {
		Var[] x = array("x", size(2 * n + 1), i -> i <= n ? dom(rangeClosed(i - n, 0)) : dom(rangeClosed(0, i - n)), "x[i] is the value of the ith variable");

		allDifferent(x);
	}
}
