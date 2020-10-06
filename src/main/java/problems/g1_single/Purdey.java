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

public class Purdey implements ProblemAPI {

	@Override
	public void model() {
		String BOYDS = "Boyds", GARVEYS = "Garveys", LOGANS = "Logans", NAVARROS = "Navarros";
		String[] families = { BOYDS, GARVEYS, LOGANS, NAVARROS };

		VarSymbolic flour = var("flour", dom(families));
		VarSymbolic kerozene = var("kerozene", dom(families));
		VarSymbolic cloth = var("cloth", dom(families));
		VarSymbolic sugar = var("sugar", dom(families));

		VarSymbolic cash = var("cash", dom(families));
		VarSymbolic credit = var("credit", dom(families));
		VarSymbolic ham = var("ham", dom(families));
		VarSymbolic peas = var("peas", dom(families));

		allDifferent(flour, kerozene, cloth, sugar);
		allDifferent(cash, credit, ham, peas);

		different(peas, LOGANS);
		different(peas, kerozene);
		disjunction(eq(kerozene, BOYDS), eq(cloth, BOYDS));
		disjunction(eq(kerozene, GARVEYS), eq(cloth, GARVEYS));
		equal(ham, flour);
		equal(credit, cloth);
		different(credit, BOYDS);
	}
}
