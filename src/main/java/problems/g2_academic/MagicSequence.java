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

public class MagicSequence implements ProblemAPI {
	int n;

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(range(n)), "x[i] is the ith value of the sequence");

		cardinality(x, range(n), occurExactly(x)).note("each value i occurs exactly x[i] times in the sequence");

		block(() -> {
			sum(x, EQ, n);
			sum(x, range(-1, n - 1), EQ, 0);
		}).tag(REDUNDANT_CONSTRAINTS);
	}
}
