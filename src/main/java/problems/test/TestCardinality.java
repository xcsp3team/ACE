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

public class TestCardinality implements ProblemAPI {

	@Override
	public void model() {
		Var x1 = var("x1", dom(1321588637, 1321588638, 1321588639, 1321588641));
		Var x2 = var("x2", dom(2147483632, 2147483633, 2147483634, 2147483637));
		Var y1 = var("y1", dom(-2147483638, -2147483637));
		Var y2 = var("y2", dom(2147483632, 2147483637));

		strictlyIncreasing(vars(x1, x2), vars(y1, y2));
	}
}
