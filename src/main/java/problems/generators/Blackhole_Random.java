/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.xcsp.modeler.problems.Blackhole;

import utility.Kit;

public class Blackhole_Random extends Blackhole {

	void data() {
		int nCardsPerSuit = imp().askInt("Number of cards per suit (e.g., 13)", "%02d");
		int nCardsPerPile = imp().askInt("Number of cards per pile (e.g., 3)", "%01d");
		int seed = imp().askInt("Seed", "%02d");
		int nCards = 4 * nCardsPerSuit, nPiles = (nCards - 1) / nCardsPerPile;
		Kit.control((nCards - 1) % nCardsPerPile == 0);
		Random rand = new Random(seed);
		List<Integer> list = IntStream.range(1, nCards).boxed().collect(Collectors.toList());
		int[][] piles = range(nPiles).range(nCardsPerPile).map((i, j) -> list.remove(rand.nextInt(list.size())));
		imp().setDataValues(nCardsPerSuit, nCardsPerPile, piles);
	}

}
