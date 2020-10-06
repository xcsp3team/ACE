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

public class TestCardinality2 implements ProblemAPI {

	@Override
	public void model() {

		Var x1 = var("x1", dom(1690164049));
		Var x2 = var("x2", dom(91234112));

		cardinality(vars(x1, x2), takingValues(2147483647, 1127478250), occurExactly(1, 0));
	}
}
