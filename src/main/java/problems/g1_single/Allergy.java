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

public class Allergy implements ProblemAPI {

	@Override
	public void model() {
		String DEBRA = "Debra", JANET = "Janet", HUGH = "Hugh", RICK = "Rick";
		String[] friends = { DEBRA, JANET, HUGH, RICK };

		VarSymbolic eggs = var("eggs", dom(friends));
		VarSymbolic mold = var("mold", dom(friends));
		VarSymbolic nuts = var("nuts", dom(friends));
		VarSymbolic ragweed = var("ragweed", dom(friends));

		VarSymbolic baxter = var("baxter", dom(friends));
		VarSymbolic lemmon = var("lemmon", dom(friends));
		VarSymbolic malone = var("malone", dom(friends));
		VarSymbolic vanfleet = var("vanfleet", dom(friends));

		allDifferent(eggs, mold, nuts, ragweed);
		allDifferent(baxter, lemmon, malone, vanfleet);

		different(mold, RICK);
		equal(eggs, baxter);
		different(lemmon, HUGH);
		different(vanfleet, HUGH);
		equal(ragweed, DEBRA);
		different(lemmon, JANET);
		different(eggs, JANET);
		different(mold, JANET);
	}
}
