/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g1_single;

import org.xcsp.common.IVar.VarSymbolic;
import org.xcsp.modeler.api.ProblemAPI;

public class Picnic implements ProblemAPI {

	@Override
	public void model() {
		String MINDY = "Mindy", SABRINA = "Sabrina", TANYA = "Tanya", ANTON = "Anton", CHET = "Chet";
		String[] friends = { MINDY, SABRINA, TANYA, ANTON, CHET };

		VarSymbolic jetski = var("jetski", dom(friends));
		VarSymbolic kayak = var("kayak", dom(friends));
		VarSymbolic canoe = var("canoe", dom(friends));
		VarSymbolic sailboard = var("sailboard", dom(friends));
		VarSymbolic sailboat = var("sailboat", dom(friends));

		VarSymbolic beer = var("beer", dom(friends));
		VarSymbolic juice = var("juice", dom(friends));
		VarSymbolic soda = var("soda", dom(friends));
		VarSymbolic water = var("water", dom(friends));
		VarSymbolic wine = var("wine", dom(friends));

		VarSymbolic bread = var("bread", dom(friends));
		VarSymbolic cheese = var("cheese", dom(friends));
		VarSymbolic cookies = var("cookies", dom(friends));
		VarSymbolic fish = var("fish", dom(friends));
		VarSymbolic salad = var("salad", dom(friends));

		allDifferent(jetski, kayak, canoe, sailboard, sailboat);
		allDifferent(beer, juice, soda, water, wine);
		allDifferent(bread, cheese, cookies, fish, salad);

		disjunction(eq(beer, MINDY), eq(soda, MINDY));
		disjunction(eq(beer, jetski), eq(soda, jetski));
		different(jetski, MINDY);

		different(kayak, CHET);
		different(fish, CHET);
		different(water, CHET);
		different(wine, CHET);
		allDifferent(kayak, fish, water, wine);

		different(salad, wine);

		disjunction(eq(canoe, SABRINA), eq(beer, SABRINA));
		disjunction(eq(canoe, cheese), eq(beer, cheese));
		different(canoe, beer);
		different(cheese, SABRINA);
		equal(set(MINDY, jetski), set(beer, soda));

		belong(bread, set(MINDY, SABRINA, TANYA));
		belong(juice, set(MINDY, SABRINA, TANYA));
		equal(bread, juice);

		different(sailboat, soda);
		different(sailboat, cookies);
		different(soda, cookies);
	}
}
