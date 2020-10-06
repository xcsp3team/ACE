/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g5_special;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class Pigeons implements ProblemAPI {
	int n; // number of pigeons

	@Override
	public void model() {
		Var[] p = array("p", size(n), dom(range(n - 1)), "p[i] is the hole where is put the ith pigeon");

		if (modelVariant(""))
			allDifferent(p);
		if (modelVariant("dec"))
			forall(range(n), i -> forall(range(i + 1, n), j -> different(p[i], p[j])));
	}
}
