/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

//java abscon.Resolution problems.patt.Fastfood ~/instances/minizinc-benchmarks-master/fast-food/ff01.dzn -f=cop => opt=3050
public class Fastfood implements ProblemAPI {
	int nDepots;
	Restaurant[] restaurants;

	class Restaurant {
		String name;
		int position;
	}

	@Override
	public void model() {
		int nRestaurants = restaurants.length;
		int[] positions = Stream.of(restaurants).mapToInt(r -> r.position).toArray();
		int[] allPositions = singleValuesIn(positions); // sorted distinct positions
		int[][] distances = range(nRestaurants).range(nRestaurants).map((i, j) -> Math.abs(positions[j] - positions[i]));

		// Var[] x = null; // array("x", size(nDepots), dom(positions), "x[i] is the position of the ith depot");
		Var[][] d = array("d", size(nRestaurants, nDepots), (i, j) -> dom(distances[i]),
				"d[i][j] is the distance between the ith restaurant and the jth depot");
		Var[] md = array("md", size(nRestaurants), i -> dom(distances[i]), "md[i] is the minimum distance between the ith restaurant and any depot");

		if (modelVariant("")) {
			Var[] x = array("x", size(nDepots), dom(range(nRestaurants)), "x[j] is the index of the restaurant used as the jth depot");

			forall(range(nRestaurants).range(nDepots), (i, j) -> element(distances[i], x[j], d[i][j]))
					.note("linking positions of depots with their distances to the restaurants");

			forall(range(nRestaurants), i -> minimum(d[i], md[i])).note("computing minimum distances");
			strictlyIncreasing(x).tag(SYMMETRY_BREAKING);

		} else if (modelVariant("table")) {
			Var[] x = array("x", size(nDepots), dom(positions), "x[i] is the position of the ith depot");

			forall(range(nRestaurants).range(nDepots), (i, j) -> {
				Table table = table().add(IntStream.of(allPositions).mapToObj(p -> tuple(p, Math.abs(p - positions[i]))));
				// System.out.println("Table " + table);
				extension(vars(x[j], d[i][j]), table);
			}).note("linking positions of depots with their distances to the restaurants");

			forall(range(nRestaurants), i -> minimum(d[i], md[i])).note("computing minimum distances");
			strictlyIncreasing(x).tag(SYMMETRY_BREAKING);
		}
		minimize(SUM, md);
	}
}