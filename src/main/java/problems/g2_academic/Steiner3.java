/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

/*
 * "A ternary Steiner system of order n is a set of n * (n-1)/6 triplets of distinct elements taking their values between 1 and n.\n" +
 * "All pairs included in two different triplets must be different.\n." +
 * "See http://www.csplib.org/Problems/prob044 and http://met.guc.edu.eg/Repository/Faculty/Publications/229/Gervet97.pdf"
 */
// TODO other models, with et vraibles, and with allDifferent-list
// 151200 solutions for oder 7
public class Steiner3 implements ProblemAPI {
	int n;

	private Table buildTable() {
		Table table = table();
		forall(range(1, n + 1).range(1, n + 1).range(1, n + 1), (i1, i2, i3) -> {
			if (i1 != i2 && i1 != i3 && i2 != i3)
				forall(range(1, n + 1).range(1, n + 1).range(1, n + 1), (j1, j2, j3) -> {
					if (j1 != j2 && j1 != j3 && j2 != j3) {
						int nb = (i1 == j1 || i1 == j2 || i1 == j3 ? 1 : 0) + (i2 == j1 || i2 == j2 || i2 == j3 ? 1 : 0)
								+ (i3 == j1 || i3 == j2 || i3 == j3 ? 1 : 0);
						if (nb <= 1) // atMostOneSharedValue
							table.add(i1, i2, i3, j1, j2, j3);
					}
				});
		});
		return table;
	}

	@Override
	public void model() {
		int nTriples = (n * (n - 1)) / 6;
		Table table = buildTable();

		Var[][] x = array("x", size(nTriples, 3), dom(rangeClosed(1, n)), "x[i] is the ith triple of values");

		forall(range(nTriples), i -> strictlyIncreasing(x[i])).note("each triple must be formed of strictly increasing integers");
		forall(range(nTriples), i -> forall(range(i + 1, nTriples), j -> extension(vars(x[i], x[j]), table)))
				.note("each pair of triples must share at most one value");
	}
}