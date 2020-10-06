/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class Vrp implements ProblemAPI {
	int n, capacity;
	int[] demand;
	int[][] distances;

	@Override
	public void model() {
		Var[][] x = array("x", size(n, n), (i, j) -> i == j ? dom(0) : dom(0, 1), "x[i][j] is 1 iff the arc (i,j) is part of a route");
		Var[] u = array("u", size(n), i -> i == 0 ? dom(0) : dom(range(capacity + 1)),
				"u[i] is the load of vehicle after visiting node i (used for subtour elimination)");

		forall(range(1, n), j -> exactly(columnOf(x, j), 1, 1)).note("exactly one incoming arc for each node j other than depot (node 0)");
		forall(range(1, n), i -> exactly(x[i], 1, 1)).note("exactly one outgoing arc for each node i other than depot (node 0)");
		forall(range(1, n).range(1, n), (i, j) -> {
			if (i != j)
				sum(vars(u[i], u[j], x[i][j]), vals(1, -1, capacity), LE, capacity - demand[j]);
		}).note("Miller-Tucker-Zemlin subtour elimination");
		forall(range(1, n), i -> greaterEqual(u[i], demand[i]));

		minimize(SUM, x, distances);
	}
}

// Below : not useful
// VarInteger in = var("in", dom(range(1, n - 1)));
// VarInteger out = var("out", dom(range(1, n - 1)));
// sum(columnOf(x, 0), EQ, in);
// sum(x[0], EQ, out);
// equal(in, out);
