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

public class TestNicolas implements ProblemAPI {

	@Override
	public void model() {

		Var[][][] z = array("z", size(4, 3, 3), dom(range(5)));

		sum(vars(z[0], z[1]), EQ, 5);

		sum((Var[]) vars(z[0], z[1], z[2]), EQ, 5);
		sum(vars(z[3][0], z[3][1]), EQ, 5);
	}
}