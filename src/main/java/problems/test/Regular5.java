/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

// class test with Mouny
public class Regular5 implements ProblemAPI {
	int n;

	@Override
	public void model() {
		if (modelVariant("m1")) {
			Var[][] x = array("x", size(n, n), (i, j) -> i != j ? dom(0, 1) : null, "x[i][j] is 1 iff edge (i,j) is present");

			forall(range(n).range(n), (i, j) -> {
				if (i != j)
					equal(x[i][j], x[j][i]);
			});
			forall(range(n), i -> sum(x[i], EQ, 5));

			instantiation(x[0], IntStream.range(0, n - 1).map(i -> i < 5 ? 1 : 0).toArray());
		}
		// if (modelVariant("m2")) {
		// Var[][] x = array("x", size(n, n), (i, j) -> i == j ? null : i > j ? dom(0) : dom(0, 1), "x[i][j] is 1 iff edge (i,j) is present");
		//
		// forall(range(n), i -> {
		// Var[] scp = range(n).provideVars(j -> i != j ? x[i][j] : null);
		// System.out.println(" i= " + i + " " + Kit.join(scp));
		// sum(scp, EQ, 5);
		// });
		//
		// }
	}
}
