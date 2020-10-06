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

public class ChangeMaking implements ProblemAPI {
	int amount;

	@Override
	public void model() {
		Var c1 = var("c1", dom(range(50)), "c1 is the number of coins of 1 cent");
		Var c5 = var("c5", dom(range(50)), "c5 is the number of coins of 5 cents");
		Var c10 = var("c10", dom(range(50)), "c10 is the number of coins of 10 cents");
		Var c20 = var("c20", dom(range(50)), "c20 is the number of coins of 20 cents");
		Var c50 = var("c50", dom(range(50)), "c50 is the number of coins of 50 cents");
		Var e1 = var("e1", dom(range(50)), "e1 is the number of coins of 1 euro");
		Var e2 = var("e2", dom(range(50)), "e2 is the number of coins of 2 euros");

		sum(vars(c1, c5, c10, c20, c50, e1, e2), vals(1, 5, 10, 20, 50, 100, 200), EQ, amount).note("the given change must be correct");
		minimize(add(c1, c5, c10, c20, c50, e1, e2)).note("the given change must have the minimum number of coins");
	}
}
