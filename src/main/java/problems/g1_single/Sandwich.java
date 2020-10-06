/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g1_single;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

// problem from INGI - LLN
public class Sandwich implements ProblemAPI {

	@Override
	public void model() {
		int alice = 0, bob = 1, sascha = 2;

		Var culprit = var("culprit", dom(range(3)), "culprit is among alice (0), bob (1) and sascha (2)");
		Var[][] liking = array("liking", size(3, 3), dom(0, 1), "liking[i][j] is 1 iff the ith guy likes the jth guy");
		Var[][] taller = array("taller", size(3, 3), dom(0, 1), "taller[i][j] is 1 iff the ith guy is taller than the jth guy");

		element(columnOf(liking, alice), culprit, 1).note("the culprit likes Alice");
		element(columnOf(taller, alice), culprit, 1).note("the culprit is taller than Alice");
		forall(range(3), i -> equal(taller[i][i], 0)).note("nobody is taller than himself");
		forall(range(3).range(3), (i, j) -> {
			if (i != j)
				different(taller[i][j], taller[j][i]);
		}).note("the ith guy is taller than the jth guy iff the jth guy is not taller than the ith guy");
		forall(range(3), i -> implication(liking[alice][i], not(liking[bob][i]))).note("Bob likes no one that Alice likes");
		forall(range(3), i -> {
			if (i != bob)
				equal(liking[alice][i], 1);
		}).note("Alice likes everybody except Bob");
		forall(range(3), i -> implication(liking[alice][i], liking[sascha][i])).note("Sascha likes everyone that Alice likes");
		forall(range(3), i -> atLeast(liking[i], 0, 1)).note("nobody likes everyone");
	}
}
