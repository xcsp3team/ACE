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

public class TestCompact implements ProblemAPI {

	@Override
	public void model() {
		Var[][] x = array("x", size(3, 3), dom(0, 1));

		allDifferent(x[0][0], x[0][1], x[0][2], x[1][0], x[1][1], x[1][2], x[2][0], x[2][1], x[2][2]);
		allDifferent(x[0][0], x[0][1], x[0][2], x[1][0], x[1][2], x[2][0], x[2][2]);
		allDifferent(x[0][0], x[0][1], x[0][2], x[1][0], x[1][1], x[2][0], x[2][2]);

	}
}
