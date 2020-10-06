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

// See Ian P. Gent, Christopher Jefferson, Ian Miguel: Watched Literals for Constraint Propagation in Minion. CP 2006: 182-197
public class LangfordBin implements ProblemAPI {
	// k = 2; // set to 2 in this model
	int n;

	@Override
	public void model() {
		Var[] v = array("v", size(2 * n), dom(range(1, n + 1)), "v[i] is the ith value of the Langford's sequence");
		Var[] p = array("p", size(2 * n), dom(range(2 * n)), "p[j] is the first (resp., second) position of 1+j/2 in v if j is even (resp., odd)");

		forall(range(n), i -> element(v, at(p[2 * i]), takingValue(i + 1)));
		forall(range(n), i -> element(v, at(p[2 * i + 1]), takingValue(i + 1)));
		forall(range(n), i -> equal(p[2 * i], add(i + 2, p[2 * i + 1])));
	}
}
