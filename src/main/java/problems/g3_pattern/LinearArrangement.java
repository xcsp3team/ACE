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

// Min Linear Arrangment (MinLA)
// java abscon.Resolution problems.soft.LinearArrangementCOP -data=MinLA04.json
public class LinearArrangement implements ProblemAPI {
	int n;
	long[][] adjacence;

	// void data() {
	// String fileName = imp().askString("Graph");
	// GraphSimpleUndirected graph = GraphSimpleUndirected.loadGraph(fileName);
	// n = graph.nNodes;
	// adjacence = graph.adjacency;
	// }

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(range(n)), "x[i] denotes the 'node' at the i-th position of the stack to be built (primal variables)");
		Var[] y = array("y", size(n), dom(range(n)), "y[i] denotes the position of the 'node' whose value is i (dual variables)");
		Var[][] d = array("d", size(n, n), (i, j) -> i < j && adjacence[i][j] == 1 ? dom(range(1, n)) : null,
				"d[i][j] denotes the distance between the ith and jth nodes (if they are adjacent)");

		allDifferent(x);
		allDifferent(y);
		channel(x, y);
		forall(range(n).range(n), (i, j) -> {
			if (d[i][j] != null)
				equal(d[i][j], dist(x[i], x[j]));
		}).note("linking primal and distance variables");

		boolean test = true;
		if (test)
			forall(range(n).range(n).range(n), (i, j, k) -> {
				if (d[i][j] != null && adjacence[i][k] == 1 && adjacence[j][k] == 1)
					intension(le(d[i][j], add(i < k ? d[i][k] : d[k][i], j < k ? d[j][k] : d[k][j])));
			}).note("triangle constraints: distance(i,j) <= distance(i,k) + distance(k,j)").tag(REDUNDANT_CONSTRAINTS);

		minimize(SUM, vars(d));

		// ((Problem) imp()).annotateValh(x, Median.class);
		// ((Problem) imp()).annotateValh(clean(vars(d)), First.class);
	}
}
