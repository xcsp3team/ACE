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

public class OscarTest implements ProblemAPI {
	int m;

	@Override
	public void model() {
		Var[] y = array("y", size(m), dom(range(m - 1)));

		forall(range(m).range(m), (i, j) -> {
			if (i < j)
				different(y[i], y[j]);
		});
	}
}
