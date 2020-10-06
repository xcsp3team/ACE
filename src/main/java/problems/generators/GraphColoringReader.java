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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.GraphColoring;
import utility.Kit;

/**
 * This is graph Dimacs coloring from the http://mat.gsia.cmu.edu/COLOR04/. These graphs are in a modification of the DIMACS file format. Each line of
 * the graph begins with a letter that defines the rest of the line. The legal lines are: c Comment: remainder of line ignored. Problem: must be of
 * form 'p edge n m' where n is the number of nodes (to be numbered 1..n) and m the number of edges. Edge: must be of the form 'e n1 n2 d' where n1
 * and n2 are the endpoints of the edge. The optional d value is used to enforce a requirement and n1 and n2 have colors that differ by at least d (if
 * there is no d value, it is assumed d=1). Fixed: of the form 'f n1 c1 c2 c3 ...' states that node n1 must choose its colors from c1, c2, c3 ... (the
 * default is that the node can take on any color). Node: of the form 'n n1 c1' used in multicoloring to state that c1 colors must be assigned to node
 * n1. Any node without a n line is assumed to have value 1. These colors must all differ by at least 1, unless there is an edge of the form 'e n1 n1
 * d' in which case all the colors at n1 must differ by at least d.
 */
public class GraphColoringReader extends GraphColoring implements ReaderTxt {

	void data() {
		scanner().findWithinHorizon("p edge", 0);
		Kit.control(hasNextInt() || scanner().findInLine(".").charAt(0) == 's');
		int nNodes = nextInt(), nEdges = nextInt(), cntEdges = 0;
		int[][] edges = new int[nEdges][];

		List<Object> colorings = new ArrayList<>();
		List<Object> multicolorings = new ArrayList<>();
		Map<Integer, Integer> nodeDistances = new HashMap<>();
		Set<Integer> fnodes = new HashSet<>(), nnodes = new HashSet<>();
		for (nextLine(); hasNextLine(); nextLine()) {
			char c = imp().fileScanner().findInLine(".").charAt(0);
			if (c != 'c') {
				if (c == 'e') {
					int n1 = nextInt() - 1, n2 = nextInt() - 1, d = hasNextInt() ? nextInt() : 1;
					// -1 because we start at 0, contrary to Dimacs format
					Kit.control(d > 0, () -> "pb with line " + c + " " + n1 + " " + n2 + " " + d);
					if (n1 == n2) {
						Kit.control(!nodeDistances.containsKey(n1));
						nodeDistances.put(n1, d);
					} else {
						int idMin = Math.min(n1, n2), idMax = Math.max(n1, n2);
						Kit.control(IntStream.range(0, cntEdges).noneMatch(i -> edges[i][0] == idMin && edges[i][1] == idMax), () -> "Pb");
						edges[cntEdges++] = new int[] { idMin, idMax, d };
					}
				}
				if (c == 'f') {
					int n = nextInt() - 1; // -1
					Utilities.control(!fnodes.contains(n), "Two occurrences of " + n);
					fnodes.add(n);
					List<Integer> list = new ArrayList<>();
					while (hasNextInt())
						list.add(nextInt() - 1); // -1 for starting colors at 0
					colorings.add(buildInternClassObject("Coloring", n, list.stream().mapToInt(i -> i).sorted().distinct().toArray()));
				}
				if (c == 'n') {
					int n = nextInt() - 1, nColors = nextInt(); // -1
					Utilities.control(!nnodes.contains(n), "Two occurrences of " + n);
					nnodes.add(n);
					multicolorings.add(buildInternClassObject("Multicoloring", n, nColors, nodeDistances.containsKey(n) ? nodeDistances.get(n) : 1));
				}
				Kit.control(c != 'n', () -> "n not taken into coount for the moment");
			}
		}
		Kit.control(cntEdges == nEdges);
		setDataValues(nNodes, edges, colorings, multicolorings);
	}
}
