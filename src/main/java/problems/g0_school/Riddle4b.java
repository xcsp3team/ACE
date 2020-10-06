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

class Riddle4b implements ProblemAPI {

	@Override
	public void model() {
		Var x[] = array("x", size(4), dom(range(15)));
		for (int i = 0; i < 3; i++)
			equal(add(x[i], 1), x[i + 1]);
		equal(add(x[0], x[1], x[2], x[3]), 14);
	}
}
