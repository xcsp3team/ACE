/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import problems.g3_pattern.Coloring;

// 250 4 4 0.8 0 
public class ColoringSmallWorld extends Coloring {

	boolean isInGraph(int[] edge, List<int[]> graph) {
		return graph.stream().anyMatch(t -> Arrays.equals(edge, t));
	}

	int[][] buildEdges(int nNodes, int nEdges, int seed, double shuffleProbability) {
		Random random = new Random(seed);
		List<int[]> ringGraph = new ArrayList<>((nNodes + 1) * nEdges);
		for (int i = 0; i < nNodes; i++)
			for (int j = 1; j <= nEdges; j++) {
				int ring = i + j >= nNodes ? i + j - nNodes : i + j < 0 ? i + j + nNodes : i + j;
				int[] t = { i, ring };
				Arrays.sort(t);
				ringGraph.add(t);
			}
		List<int[]> randomGraph = new ArrayList<>((nNodes + 1) * nEdges);
		for (int v = 0; v < nNodes; v++) {
			for (int i = 1; i <= nEdges; i++) {
				int[] edge = new int[2];
				do {
					edge[0] = random.nextInt(nNodes);
					do {
						edge[1] = random.nextInt(nNodes);
					} while (edge[0] == edge[1]);
					Arrays.sort(edge);
				} while (isInGraph(edge, randomGraph));
				randomGraph.add(edge);
			}
		}
		// Shuffle !
		List<int[]> graph = new ArrayList<>((nNodes + 1) * nEdges);
		List<Integer> removed = new ArrayList<>();
		for (int i = 0; i < ringGraph.size(); i++)
			if (random.nextDouble() < shuffleProbability)
				removed.add(i);
			else
				graph.add(ringGraph.get(i));
		for (int i : removed)
			if (!isInGraph(randomGraph.get(i), graph))
				graph.add(randomGraph.get(i));
			else if (!isInGraph(ringGraph.get(i), graph))
				graph.add(ringGraph.get(i));
		return graph.stream().toArray(int[][]::new);
	}

	void data() {
		int nNodes = imp().askInt("Number of nodes");
		int nEdges = imp().askInt("Number of edges");
		int nColors = imp().askInt("Number of colors");
		double shuffleProbability = imp().askDouble("Shuffle probability", v -> 0.0 <= v && v <= 1.0);
		int seed = imp().askInt("Seed");
		int[][] edges = buildEdges(nNodes, nEdges, seed, shuffleProbability);
		imp().setDataValues(nNodes, nColors, edges);
	}

}
