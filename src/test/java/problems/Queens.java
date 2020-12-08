/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class Queens implements ProblemAPI {
	int n; // number of queens

	@Override
	public void model() {
		Var[] q = array("q", size(n), dom(range(n)), "q[i] is the column where is put the ith queen (at row i)");

		if (modelVariant("")) {
			allDifferent(q);
			allDifferent(treesFrom(range(n), i -> add(q[i], i))).note("controlling no two queens on the same upward diagonal");
			allDifferent(treesFrom(range(n), i -> sub(q[i], i))).note("controlling no two queens on the same downward diagonal");
		}
		if (modelVariant("v1")) {
			allDifferent(q);
			forall(range(n), i -> forall(range(i + 1, n), j -> different(abs(sub(q[i], q[j])), j - i)));
		}
		if (modelVariant("v2")) {
			forall(range(n), i -> forall(range(i + 1, n), j -> conjunction(ne(q[i], q[j]), ne(abs(sub(q[i], q[j])), j - i))));
		}
		if (modelVariant("v3")) {
			forall(range(n), i -> forall(range(i + 1, n), j -> different(q[i], q[j])));
			forall(range(n), i -> forall(range(i + 1, n), j -> different(dist(i, j), dist(q[i], q[j]))));
		}
		if (modelVariant("v4")) {
			allDifferent(q);
			forall(range(n), i -> forall(range(i + 1, n), j -> conjunction(ne(q[i], q[j]), ne(dist(q[i], q[j]), dist(i, j)))));
		}
		if (modelVariant("v5")) {
			allDifferent(q);
			Var[] a = array("a", size(n), dom(range(2 * n - 1)));
			Var[] s = array("s", size(n), dom(rangeClosed(-n + 1, n - 1)));
			forall(range(n), i -> equal(add(q[i], i), a[i]));
			forall(range(n), i -> equal(sub(q[i], i), s[i]));
			allDifferent(a).note("controlling no two queens on the same upward diagonal");
			allDifferent(s).note("controlling no two queens on the same downward diagonal");
		}

	}
}

// Two alternatives to the forall of model m1
// forall(range(n).range(n), (i, j) -> {
// if (i < j)
// different(dist(i, j), dist(q[i], q[j]));
// });

// for (int i = 0; i < n; i++)
// for (int j = i + 1; j < n; j++)
// different(dist(i, j), dist(q[i], q[j]));

// allDifferent(range(n).provideObjects(i -> add(q[i], i))); // compilable under Eclipse but not with Oracle javac
// allDifferent(range(n).provideObjects(i -> sub(q[i], i)));
