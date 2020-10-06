/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g1_single;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

class Witch implements ProblemAPI {

	@Override
	public void model() {
		Var x = var("x", dom(range(400)), "x is the number of magic potions for love");
		Var y = var("y", dom(range(400)), "y is the number of magic potions for youth");

		sum(vars(x, y), vals(3, 2), LE, 800);
		sum(vars(x, y), vals(1, 3), LE, 700);
		sum(vars(x, y), vals(1, 2), LE, 400);

		maximize(add(mul(4, x), mul(5, y)));
	}
}