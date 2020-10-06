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

public class Langford implements ProblemAPI {
	int k; // number of sets/occurrences
	int n; // number of values

	@Override
	public void model() {
		Var[][] x = array("x", size(k, n), dom(range(k * n)), "x[i][j] is the position in the sequence of the ith occurrence of j+1");

		allDifferent(x).note("all positions of the sequence must be set");
		forall(range(k - 1).range(n), (i, j) -> equal(x[i + 1][j], add(x[i][j], j + 2))).note("there are j numbers between two occurrences of j");
	}
}
