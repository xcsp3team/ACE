/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class BigLeq implements ProblemAPI {
	int n;

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(range(n)));
		forall(range(n - 1), i -> intension(le(x[i], x[i + 1])));
		allDifferent(x);
	}
}
