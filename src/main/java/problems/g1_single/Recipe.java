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

// Recipe from Minizinc tutorial.
public class Recipe implements ProblemAPI {

	@Override
	public void model() {
		Var b = var("b", dom(range(100)), "b is the number of banana cakes");
		Var c = var("c", dom(range(100)), "c is the number of chocolate cakes");

		intension(le(add(mul(250, b), mul(200, c)), 4000)).note("using at most 4000 grams of flour");
		intension(le(mul(2, b), 6)).note("using at most 6 bananas");
		intension(le(add(mul(75, b), mul(150, c)), 2000)).note("using at most 2000 grams of sugar");
		intension(le(add(mul(100, b), mul(150, c)), 500)).note("using at most 500 grams of butter");
		intension(le(mul(75, c), 500)).note("using at most 500 grams of cocoa");

		// sum(vars(b, c), vals(250, 200), LE, 4000);
		// sum(vars(b, c), vals(75, 150), LE, 2000);
		// sum(vars(b, c), vals(100, 150), LE, 500);

		maximize(add(mul(400, b), mul(450, c))).note("maximizing the profit (400 and 450 cents for each banana and chocolate cake, respectively");
	}

}