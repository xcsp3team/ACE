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

public class ArbreExam2017 implements ProblemAPI {

	@Override
	public void model() {
		Var w = var("w", dom(1, 2, 3));
		Var x = var("x", dom(1, 2, 3));
		Var y = var("y", dom(1, 2, 3));
		Var z = var("z", dom(1, 2, 3));

		greaterEqual(w, x);
		greaterEqual(x, y);
		greaterEqual(y, z);
		different(w, z);
		extension(vars(x, z), table("(1,3)(2,2)(3,1)"));
	}
}