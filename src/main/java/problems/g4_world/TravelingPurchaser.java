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

public class TravelingPurchaser implements ProblemAPI {

	int[][] cityDistances, productPrices;

	@Override
	public void model() {
		int nCities = cityDistances.length, nProducts = productPrices.length;

		Var[] s = array("s", size(nCities), dom(range(nCities)), "s[i] is the city succeeding to the ith city (itself if not part of the route)");
		Var[] d = array("d", size(nCities), i -> dom(cityDistances[i], v -> v >= 0),
				"d[i] is the distance (seen as a travel cost) between the ith city and its successor");
		Var[] l = array("l", size(nProducts), dom(range(nCities - 1)), "l[i] is the purchase location of the ith product (last city has nothing for sale)");
		Var[] c = array("c", size(nProducts), i -> dom(productPrices[i]), "c[i] is the purchase cost of the ith product");

		if (modelVariant("")) {
			forall(range(nCities), i -> element(cityDistances[i], s[i], d[i])).note("linking distances to successors");
			forall(range(nProducts), i -> element(productPrices[i], l[i], c[i])).note("linking purchase locations to purchase costs");
			forall(range(nCities).range(nProducts), (i, j) -> implication(eq(s[i], i), ne(l[j], i)))
					.note("purchasing a product at a city is only possible if you visit that city");
		} else if (modelVariant("ext")) {
			// forall(range(nCities), i -> extension(vars(s[i], d[i]), number(distances[i], j -> distances[i][j] >= 0))).note("Linking
			// distances to successors");
			// forall(range(nProducts), i -> extension(vars(l[i], c[i]), number(prices[i]))).note("Linking purchase locations to
			// purchase costs");
			// pour le dernier forall, alternative smart table : i !=i !=i ... !=i | !=i i * ... * | !=i * i ... * ...

		}
		circuit(s);
		different(s[nCities - 1], (nCities - 1)).note("last city must be visited (we start here)");

		minimize(SUM, vars(d, c));
	}
}