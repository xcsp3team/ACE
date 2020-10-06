/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import org.xcsp.common.IVar.VarSymbolic;
import org.xcsp.modeler.api.ProblemAPI;

public class TestSymbolic implements ProblemAPI {

	@Override
	public void model() {
		String RED = "red", YELLOW = "yellow", BLUE = "blue", PINK = "pink";
		String[][] tuples = { { YELLOW, RED }, { BLUE, YELLOW }, { RED, RED }, { YELLOW, PINK } };

		VarSymbolic w = var("w", dom(PINK, RED, YELLOW));
		VarSymbolic x = var("x", dom(RED, YELLOW, BLUE));
		VarSymbolic y = var("y", dom(RED, YELLOW, BLUE));
		VarSymbolic z = var("z", dom(RED, YELLOW, BLUE));

		equal(x, y);
		different(x, z);
		greaterThan(y, z);
		intension(or(eq(y, RED), eq(w, z)));
		intension(xor(eq(x, YELLOW), eq(y, RED), eq(z, YELLOW)));
		extension(vars(x, w), tuples);
		extension(z, RED, YELLOW);
		extension(w, RED, YELLOW);
	}
}
