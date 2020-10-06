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
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;
import org.xcsp.modeler.entities.CtrEntities.CtrEntity;

import constraints.CtrHard;
import problem.Problem;
import utility.Kit;

public class TestBuildTable implements ProblemAPI {

	@Override
	public void model() {
		Var w = var("w", dom(rangeClosed(1, 10)));
		Var x = var("x", dom(rangeClosed(1, 10)));
		Var y = var("y", dom(rangeClosed(1, 10)));
		// Var z = var("z", dom(range(1, 10)));

		CtrEntity c1 = lessEqual(w, x); // w.lessThan(x);
		CtrEntity c2 = lessEqual(x, y);
		CtrEntity c3 = equal(w, y);

		int[][] t = ((Problem) imp()).buildTable((CtrHard) ((CtrAlone) c1).ctr, (CtrHard) ((CtrAlone) c2).ctr, (CtrHard) ((CtrAlone) c3).ctr);
		System.out.println("Tuples = " + Kit.join(t));
	}
}