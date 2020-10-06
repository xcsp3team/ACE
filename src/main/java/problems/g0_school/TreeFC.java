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

public class TreeFC implements ProblemAPI {

	@Override
	public void model() {
		Var x1 = var("x1", dom(0, 1, 2, 3));
		Var x2 = var("x2", dom(0, 1, 2, 3));
		Var x3 = var("x3", dom(0, 1, 2, 3));
		Var x4 = var("x4", dom(2, 3));
		Var x5 = var("x5", dom(2, 3));

		different(x1, x2);
		different(x1, x3);
		different(x2, x3);
		different(x2, x4);
		different(x2, x5);
		different(x3, x4);
		different(x3, x5);
		different(x4, x5);
	}
}