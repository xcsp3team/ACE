/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

// 250 4 4 0.8 0 
public class Coloring implements ProblemAPI {
	int nNodes, nColors;
	int[][] edges;

	@Override
	public void model() {
		int nEdges = edges.length;
		Var[] x = array("x", size(nNodes), dom(range(nColors)), "x[i] is the color assigned to the ith node of the graph");

		forall(range(nEdges), i -> different(x[edges[i][0]], x[edges[i][1]])).note("two adjacent nodes must be colored differently");

		if (modelVariant("csp"))
			forall(range(Math.min(nNodes, nColors)), i -> lessEqual(x[i], i)).tag(SYMMETRY_BREAKING);
		else
			minimize(MAXIMUM, x).note("minimizing the maximum used color index (and, consequently, the number of colors)");
	}
}
