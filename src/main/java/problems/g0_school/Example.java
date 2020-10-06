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

public class Example implements ProblemAPI {

	@Override
	public void model() {
		Var w = var("w", dom(range(1, 4)));
		Var x = var("x", dom(range(1, 4)));
		Var y = var("y", dom(range(1, 5)));
		Var z = var("z", dom(range(1, 5)));

		equal(x, y);
		lessEqual(x, add(y, 1));
		greaterEqual(y, add(w, z));
		extension(vars(x, z), table("(1,2)(2,1)(2,4)(3,3)"));
	}
}
