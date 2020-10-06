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

// The code is for graphs Kk × Pp that consist of p copies of a clique Kk with corresponding nodes of the cliques also forming the nodes of a path of length p
public class GracefulGraph implements ProblemAPI {
	int k; // size of each clique K (number of nodes)
	int p; // size of each path P (or equivalently, number of cliques)

	@Override
	public void model() {
		int nEdges = ((k * (k - 1)) * p) / 2 + k * (p - 1);

		Var[][] cn = array("cn", size(p, k), dom(range(nEdges + 1)), "cn[i][j] is the color of the jth node of the ith clique");
		Var[][][] ce = array("ce", size(p, k, k), (i, j1, j2) -> dom(range(1, nEdges + 1)).when(j1 < j2),
				"ce[i][j1][j2] is the color of the edge (j1,j2) of the ith clique, for j1 strictly less than j2");
		Var[][] cp = array("cp", size(p - 1, k), dom(range(1, nEdges + 1)), "cp[i][j] is the color of the jth edge of the ith path");

		allDifferent(cn).note("all nodes are colored differently");
		allDifferent(vars(ce, cp)).note("all edges are colored differently");

		block(() -> {
			forall(range(p).range(k), (i, j1) -> forall(range(j1 + 1, k), j2 -> equal(ce[i][j1][j2], dist(cn[i][j1], cn[i][j2]))));
			forall(range(p - 1).range(k), (i, j) -> equal(cp[i][j], dist(cn[i][j], cn[i + 1][j])));
		}).note("computing colors of edges from colors of nodes");

	}
}