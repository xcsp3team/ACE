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

public class TestAllDiff implements ProblemAPI {

	@Override
	public void model() {
		Var x0 = var("x0", dom(340794, 340798, 340799, 340801, 340802));
		Var x1 = var("x1", dom(999998, 1000000));
		Var x2 = var("x2", dom(91775, 91776, 91780));
		Var x3 = var("x3", dom(1000000));
		allDifferent(x0, x1, x2, x3);
	}
}
