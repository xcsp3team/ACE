/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

public class Subisomorphism implements ProblemAPI { // subgraph isomorphism problem
	int nPatternNodes, nTargetNodes;
	int[][] patternEdges, targetEdges;

	private int[] selfLoops(int[][] edges) {
		return Stream.of(edges).filter(t -> t[0] == t[1]).mapToInt(t -> t[0]).toArray();
	}

	private int degree(int[][] edges, int node) {
		return (int) Stream.of(edges).filter(t -> t[0] == node || t[1] == node).count();
	}

	private Table bothWayTable() {
		Table table = table();
		table.add(targetEdges);
		table.add(Stream.of(targetEdges).map(t -> tuple(t[1], t[0]))); // reversed tuples
		return table;
	}

	@Override
	public void model() {
		int[] pLoops = selfLoops(patternEdges);
		int[] tLoops = selfLoops(targetEdges);
		int[] pDegrees = range(nPatternNodes).map(i -> degree(patternEdges, i));
		int[] tDegrees = range(nTargetNodes).map(i -> degree(targetEdges, i));

		Var[] x = array("x", size(nPatternNodes), dom(range(nTargetNodes)), "x[i] is the target node to which the ith pattern node is mapped");

		allDifferent(x).note("ensuring injectivity");

		Table bothWayTable = bothWayTable();
		forall(range(patternEdges.length), i -> extension(vars(x[patternEdges[i][0]], x[patternEdges[i][1]]), bothWayTable)).note("preserving edges");

		forall(range(pLoops.length), i -> extension(x[pLoops[i]], tLoops)).note("being careful of self-loops");

		forall(range(nPatternNodes), i -> {
			int[] conflicts = range(nTargetNodes).select(j -> tDegrees[j] < pDegrees[i]);
			if (conflicts.length > 0)
				extension(x[i], conflicts, NEGATIVE);
		}).tag(REDUNDANT_CONSTRAINTS);
	}
}