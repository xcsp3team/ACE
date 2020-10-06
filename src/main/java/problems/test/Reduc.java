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

public class Reduc implements ProblemAPI {

	@Override
	public void model() {
		Var x = var("x", dom(0, 1, 2));
		Var[] t = array("t", size(100), dom(range(21)));
		// Var[] z = array("z", size(20), i -> i % 2 == 0 ? dom(range(1, 10)) : null);

		different(x, t[0]);
		forall(range(t.length - 1), i -> equal(t[i], t[i + 1]));
	}
}