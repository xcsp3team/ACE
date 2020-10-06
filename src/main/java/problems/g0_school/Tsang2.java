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

public class Tsang2 implements ProblemAPI {
	@Override
	public void model() {
		Var w = var("w", dom(range(1, 6)));
		Var x = var("x", dom(range(2, 7)));
		Var y = var("y", dom(range(3, 8)));
		Var z = var("z", dom(range(4, 9)));

		extension(vars(w, x), table("(1,2)(5,6)"));
		extension(vars(x, y), table("(2,3)(6,7)"));
		extension(vars(y, z), table("(3,4)(7,8)"));
		extension(vars(z, w), table("(4,1)(8,5)"));
	}
}
