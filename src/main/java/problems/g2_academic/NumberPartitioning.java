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
import org.xcsp.modeler.api.ProblemAPI;

// Pb 049 in CSPLib
public class NumberPartitioning implements ProblemAPI {
	int n;

	@Override
	public void model() {
		control(n % 2 == 0, "The value of n must be even");

		Var[] x = array("x", size(n / 2), dom(rangeClosed(1, n)), "x[i] is the ith value of the first set");
		Var[] y = array("y", size(n / 2), dom(rangeClosed(1, n)), "y[i] is the ith value of the second set");
		// Var[] cx = array("cx", size(n / 2), dom(rangeClosed(1, n * n)), "cx[i] is the square of the ith value of the first set");
		// Var[] cy = array("cy", size(n / 2), dom(rangeClosed(1, n * n)), "cy[i] is the square of the ith value of the second set");

		allDifferent(vars(x, y));
		block(() -> {
			sum(x, EQ, n * (n + 1) / 4);
			sum(y, EQ, n * (n + 1) / 4);
		}).tag("power1");
		block(() -> {
			// forall(range(n / 2), i -> equal(cx[i], mul(x[i], x[i])));
			// forall(range(n / 2), i -> equal(cy[i], mul(y[i], y[i])));
			sum(treesFrom(range(n / 2), i -> mul(x[i], x[i])), EQ, n * (n + 1) * (2 * n + 1) / 12);
			sum(treesFrom(range(n / 2), i -> mul(y[i], y[i])), EQ, n * (n + 1) * (2 * n + 1) / 12);
		}).tag("power2");
		block(() -> {
			equal(x[0], 1);
			strictlyIncreasing(x);
			strictlyIncreasing(y);
		}).tag(SYMMETRY_BREAKING);
	}
}