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

public class TestLC implements ProblemAPI {

	@Override
	public void model() {
		Var[] x = array("x", size(7), i -> i == 0 || i == 2 || i == 3 ? dom(0, 1) : dom(0, 1, 2));

		different(x[1], x[4]);
		different(x[1], x[5]);
		different(x[1], x[6]);
		different(x[4], x[5]);
		different(x[4], x[6]);
		different(x[5], x[6]);
	}
}
