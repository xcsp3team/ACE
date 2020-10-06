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

public class Mysterious implements ProblemAPI {

	@Override
	public void model() {
		Var x = var("x", dom(range(6)));
		Var y = var("y", dom(range(6)));
		Var z = var("z", dom(range(6)));

		greaterThan(x, y);
		different(x, z);
		greaterThan(y, z);
	}
}
