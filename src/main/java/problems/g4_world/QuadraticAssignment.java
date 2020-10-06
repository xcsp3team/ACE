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
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

public class QuadraticAssignment implements ProblemAPI {
	int[][] weights; // facility weights
	int[][] distances; // location distances

	private Table channelingTable() {
		Table table = table();
		for (int i = 0; i < distances.length; i++)
			for (int j = 0; j < distances.length; j++)
				if (i != j)
					table.add(i, j, distances[i][j]);
		return table;
	}

	@Override
	public void model() {
		int n = weights.length;

		Var[] x = array("x", size(n), dom(range(n)), "x[i] is the location assigned to the ith facility");
		Var[][] d = array("d", size(n, n), (i, j) -> dom(distances).when(i < j && weights[i][j] != 0),
				"d[i][j] is the distance between the locations assigned to the ith and jth facilities");

		allDifferent(x).note("all locations must be different");

		Table table = channelingTable();
		forall(range(n).range(n), (i, j) -> {
			if (i < j && weights[i][j] != 0)
				extension(vars(x[i], x[j], d[i][j]), table);
		}).note("computing the distances");

		minimize(SUM, d, weightedBy(weights), (i, j) -> i < j && weights[i][j] != 0).note("minimizing summed up distances multiplied by flows");
	}
}

// int[][] tuples = select(number(locationDistances), (int[] t) -> t[0] != t[1]);
