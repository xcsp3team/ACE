/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class TestNoOverlap implements ProblemAPI {

	@Override
	public void model() {
		Var[][] x = array("x", size(3, 2), dom(0, 1, 2));

		// noOverlap(x, table("(1,2)(2,1)(1,1)").collected());
		noOverlap(x, vals(1, 2), vals(2, 1), vals(1, 1));
	}
}
