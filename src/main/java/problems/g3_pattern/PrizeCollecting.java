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

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

import problem.Problem;

// 15-3-5-0.dzn => optimum 20 in 3s
public class PrizeCollecting implements ProblemAPI {
	int n;
	int[][] prizes;

	@Override
	public void model() {
		Var[] s = array("s", size(n), dom(range(-1, n)), "s[i] is the node that succeeds to node i in tour (0 for last edge and -1 for unused)");
		Var[] p = array("p", size(n), dom(range(-1, n)), "p[i] is the position of node i in the tour (-1 if not in the tour)");
		Var[] g = array("g", size(n), i -> dom(prizes[i]), "g[i] is the gain obtained from node i in the tour");

		equal(p[0], 0);
		forall(range(n), i -> equivalence(gt(p[i], -1), gt(s[i], -1))).note("If used, the next position in tour is not -1");

		// boolean test = true;
		// if (test) {
		// forall(range(n), i -> {
		// ifThen(greaterThan(s[i], 0), element(s[i], p, add(p[i],1))); // use a view or an attribute startResult
		// }); // } else
		forall(range(n), i -> {
			int[] t1 = range(n + 1).map(j -> j == 0 ? -1 : STAR), t2 = range(n + 1).map(j -> j == 0 ? 0 : STAR); // because -1 and 0 are managed apart
			int[][] m = ((Problem) imp()).jokerTableForElement(p, s[i], p[i], 1);
			int[][] table = IntStream.range(0, m.length + 2).filter(j -> j < 2 || m[j - 2][0] != 0).mapToObj(j -> j == 0 ? t1 : j == 1 ? t2 : m[j - 2])
					.toArray(int[][]::new); // removing useless tuples from m (though we could have kept them) subsumed by t2
			extension(vars(s[i], p), Table.clean(table));
		}).note("Linking s and p");

		forall(range(n), i -> atMost(s, i, 1)).note("at most one node with i (different from 0) as its successor");
		forall(range(n), i -> element(prizes[i], startIndex(-1), index(s[i]), g[i])).note("managing gains"); // for saving into extension,
																												// add 0 as parameter

		maximize(SUM, g);
	}
}
