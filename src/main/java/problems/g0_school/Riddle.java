/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g0_school;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

class Riddle implements ProblemAPI {

	@Override
	public void model() {
		Var x1 = var("x1", dom(range(15)));
		Var x2 = var("x2", dom(range(15)));
		Var x3 = var("x3", dom(range(15)));
		Var x4 = var("x4", dom(range(15)));

		equal(add(x1, 1), x2);
		equal(add(x2, 1), x3);
		equal(add(x3, 1), x4);
		equal(add(x1, x2, x3, x4), 14);
	}
}
