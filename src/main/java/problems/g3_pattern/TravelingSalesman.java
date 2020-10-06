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
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

public class TravelingSalesman implements ProblemAPI {
	int[][] distances;

	@Override
	public void model() {
		int nCities = distances.length;

		Var[] c = array("c", size(nCities), dom(range(nCities)), "c[i] is the ith city of the tour");
		Var[] d = array("d", size(nCities), dom(distances), "d[i] is the distance between the cities i and i+1");

		allDifferent(c).note("Visiting each city only once");

		if (modelVariant(""))
			forall(range(nCities), i -> element(distances, 0, c[i], 0, c[(i + 1) % nCities], d[i]))
					.note("computing the distance between any two successive cities in the tour");
		else if (modelVariant("table")) {
			Table table = table().addFrom(range(nCities).range(nCities), (i, j) -> i == j ? null : tuple(i, j, distances[i][j]));
			forall(range(nCities), i -> extension(vars(c[i], c[(i + 1) % nCities], d[i]), table))
					.note("computing the distance between any two successive cities in the tour");
		}

		minimize(SUM, d);
	}
}

// private Table distTable() {
// Table table = table();
// for (int i = 0; i < distances.length; i++)
// for (int j = 0; j < distances.length; j++)
// if (i != j)
// table.add(i, j, distances[i][j]);
// return table;
// }
//
//
// private Table distTable() {
// Table table = table();
// ~forall~(range(distances.length).range(distances.length), (i, j) -> table.addIf(i != j, tuple(i, j, distances[i][j])));
// return table;
// }