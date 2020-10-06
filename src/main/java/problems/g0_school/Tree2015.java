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

public class Tree2015 implements ProblemAPI {

	@Override
	public void model() {
		Var u = var("u", dom(0, 1, 2));
		Var v = var("v", dom(0, 1, 2));
		Var w = var("w", dom(0, 1, 2));
		Var x = var("x", dom(0, 1));
		Var y = var("y", dom(0, 1));
		Var z = var("z", dom(0, 1));

		equal(u, v);
		different(u, w);
		different(v, w);
		different(w, x);
		equal(w, y);
		different(x, y);
		different(x, z);
		different(y, z);
	}
}