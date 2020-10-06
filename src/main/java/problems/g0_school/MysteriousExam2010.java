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

public class MysteriousExam2010 implements ProblemAPI {

	@Override
	public void model() {
		Var v = var("v", dom(1, 2, 3));
		Var w = var("w", dom(1, 2, 3));
		Var x = var("x", dom(1, 2, 3));
		Var y = var("y", dom(2, 3));
		Var z = var("z", dom(2, 3));

		different(v, w);
		different(v, x);
		different(x, y);
		different(y, z);
		different(x, z);
	}
}
