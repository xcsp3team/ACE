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

public class Pic2 implements ProblemAPI {

	@Override
	public void model() {
		Var x = var("x", dom(0, 1));
		Var y = var("y", dom(0, 1));
		Var z = var("z", dom(0, 1));

		extension(vars(x, y), table("(0,0)(1,1)"));
		extension(vars(x, z), table("(0,0)(1,1)"));
		extension(vars(y, z), table("(0,1)(1,0)"));
	}
}