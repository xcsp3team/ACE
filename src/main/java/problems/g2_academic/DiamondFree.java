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

// Pb050 in CSPLib
public class DiamondFree implements ProblemAPI {
	int n;

	@Override
	public void model() {
		Var[][] x = array("x", size(n, n), (i, j) -> i != j ? dom(0, 1) : dom(0), "x is the adjacency matrix");
		Var[] y = array("y", size(n), dom(range(1, n).select(i -> i % 3 == 0)), "y[i] is the degree of the ith node");
		Var s = var("s", dom(range(n, n * (n - 1) + 1).select(i -> i % 12 == 0)), "s is the sum of all degrees");

		forall(range(n).range(n).range(n).range(n), (i, j, k, l) -> {
			if (i < j && j < k && k < l)
				sum(vars(x[i][j], x[i][k], x[i][l], x[j][k], x[j][l], x[k][l]), LE, 4);
		}).note("ensuring the absence of diamond in the graph");
		forall(range(n).range(n), (i, j) -> {
			if (i != j)
				equal(x[i][j], x[j][i]);
		}).note("ensuring that the graph is undirected (symmetric)");
		forall(range(n), i -> sum(x[i], EQ, y[i])).note("computing node degrees");
		sum(y, EQ, s).note("computing the sum of node degrees");

		block(() -> {
			decreasing(y);
			increasing(x);
		}).tag(SYMMETRY_BREAKING);

	}
}
