/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import problems.g3_pattern.Coloring;
import tools.random.RandomGeneration.RandomGenerationProp;
import tools.random.RandomGeneration.RandomGenerationProp.TypeList;

public class Coloring_Random extends Coloring {

	void data() {
		int nNodes = imp().askInt("Number of nodes");
		int nEdges = imp().askInt("Number of edges");
		int seed = imp().askInt("Seed");
		int[][] edges = new RandomGenerationProp(nNodes, 2, seed).selectSets(nEdges, TypeList.CONNECTED, false);
		imp().setDataValues(nNodes, nEdges, nNodes, edges);
	}

}
