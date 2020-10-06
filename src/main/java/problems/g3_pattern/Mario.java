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

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.predicates.XNode;
import org.xcsp.modeler.api.ProblemAPI;

public class Mario implements ProblemAPI {
	int marioHouse, luigiHouse;
	int fuelLimit;
	House[] houses;

	class House {
		int[] fuelConsumption;
		int gold;
	}

	@Override
	public void model() {
		int nHouses = houses.length;
		int[][] fuels = IntStream.range(0, nHouses).mapToObj(i -> houses[i].fuelConsumption).toArray(int[][]::new);

		Var[] s = array("s", size(nHouses), dom(range(nHouses)), "s[i] is the house succeeding to the ith house (itself if not part of the route)");
		Var[] f = array("f", size(nHouses), i -> dom(houses[i].fuelConsumption), "f[i] is the fuel consumed at each step (from house i to its successor)");
		// Var[] g = array("g", size(nHouses), i -> houses[i].gold == 0 ? dom(0) : dom(0, houses[i].gold), "g[i] is the gold earned at house i");

		if (modelVariant("table"))
			forall(range(nHouses), i -> extension(vars(s[i], f[i]), indexing(houses[i].fuelConsumption))).note("fuel consumption at each step");
		else
			forall(range(nHouses), i -> element(fuels[i], s[i], f[i])).note("fuel consumption at each step");

		sum(f, LE, fuelLimit).note("we cannot consume more than the available fuel");

		// forall(range(nHouses), i -> {
		// if (i != marioHouse && i != luigiHouse) equivalence(eq(s[i], i), eq(g[i], 0));
		// }).note("gold earned at each house");

		circuit(s).note("Mario must make a tour (not necessarily complete)");
		equal(s[luigiHouse], marioHouse).note("Mario's house succeeds to Luigi's house");

		Stream<XNode<IVar>> trees = IntStream.range(0, nHouses).filter(i -> i != marioHouse && i != luigiHouse).mapToObj(i -> ne(s[i], i));

		// treesFrom(range(nHouses), i -> i != marioHouse && i != luigiHouse ? ne(s[i], i) : null);
		int[] coeffs = IntStream.range(0, nHouses).filter(i -> i != marioHouse && i != luigiHouse).map(i -> houses[i].gold).toArray();
		maximize(SUM, trees, coeffs).note("maximizing collected gold"); // sum(g)
	}
}
