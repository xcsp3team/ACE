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
import org.xcsp.modeler.api.ProblemAPI;

public class GraphColoring implements ProblemAPI {
	int nNodes;
	int[][] edges;
	Coloring[] colorings;
	Multicoloring[] multicolorings;

	class Coloring {
		int node;
		int[] colors;
	}

	class Multicoloring {
		int node;
		int nColors;
		int distance;
	}

	@Override
	public void model() {
		// TODO multicoloring
		int nEdges = edges.length;

		Var[] c = array("c", size(nNodes), dom(range(nNodes)), "c[i] is the color assigned to the ith node");

		forall(range(nEdges), i -> {
			Var x = c[edges[i][0]], y = c[edges[i][1]];
			intension(edges[i][2] == 1 ? ne(x, y) : ge(dist(x, y), edges[i][2]));
		});

		if (colorings != null && colorings.length > 0) {
			Coloring[] gt1 = Stream.of(colorings).filter(cl -> cl.colors.length > 1).toArray(Coloring[]::new);
			Coloring[] eq1 = Stream.of(colorings).filter(cl -> cl.colors.length == 1).toArray(Coloring[]::new);
			forall(range(gt1.length), i -> extension(c[gt1[i].node], gt1[i].colors)).note("nodes with subsets of prefixed colors");
			instantiation(Stream.of(eq1).map(cl -> c[cl.node]), Stream.of(eq1).mapToInt(cl -> cl.colors[0])).note("nodes with preassigned colors");
		}

		if (modelVariant("sum"))
			minimize(SUM, c).note("minimizing the sum of colors assigned to nodes");
		else
			minimize(MAXIMUM, c);
	}
}
