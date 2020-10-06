/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g0_school;

import org.xcsp.common.IVar.VarSymbolic;
import org.xcsp.modeler.api.ProblemAPI;

public class SimpleColoring implements ProblemAPI {

	@Override
	public void model() {
		VarSymbolic[] x = arraySymbolic("x", size(4), dom("b", "g", "r"));

		forall(range(4).range(4), (i, j) -> {
			if (i < j)
				different(x[i], x[j]);
		});
	}
}
