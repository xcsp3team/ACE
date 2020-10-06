/**
1 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g5_special;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

/**
 * Problem propose d
 */
public class AllIntervalJC implements ProblemAPI {

	int n; // order

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(range(n)), "x[i] is the ith value of the series");
		Var[] y = array("y", size(n - 1), dom(range(1, n)), "y[i] is the distance between x[i] and x[i+1]");

		allDifferent(x);
		allDifferent(y);

		forall(range(n - 1), i -> extension(eq(y[i], dist(x[i], x[i + 1]))));
	}
}
