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
 * "Ramsey problem.\n" + "It is to colour the edges of a complete graph with n nodes using at most k colours.\n" +
 * "There must be no monochromatic triangle in the graph, i.e. in any triangle at most two edges have the same colour.\n" +
 * "With 3 colours, the problem has a solution if n < 17."
 */
public class Ramsey implements ProblemAPI {
	int n;

	@Override
	public void model() {
		Var[][] x = array("x", size(n, n), (i, j) -> dom(range((n * (n - 1)) / 2)).when(i < j), "x[i][j] is the color of the edge between nodes i and j");

		forall(range(n).range(n).range(n), (i, j, k) -> {
			if (i < j && j < k)
				notAllEqual(x[i][j], x[i][k], x[j][k]);
		}).note("no monochromatic triangle in the graph");
		minimize(MAXIMUM, x);
	}
}
