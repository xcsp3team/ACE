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

import constraints.hard.extension.CtrExtensionMDD;
import constraints.hard.global.SumWeighted.SumWeightedGE;
import problem.Problem;
import variables.Variable;

public class FilteringGlobal implements ProblemAPI {

	private int test = 3;

	Var[] x = test == 1 ? vars(var("w", dom(1, 2, 3)), var("x", dom(1, 2, 3)), var("y", dom(2, 3, 4)), var("z", dom(2, 3, 4)))
			: test == 2 ? array("x", size(6), dom(1, 2, 3, 4)) : array("x", size(3), dom(1, 2));

	@Override
	public void model() {
		if (test == 1)
			((Problem) imp()).addCtr(new SumWeightedGE(((Problem) imp()), (Variable[]) x, vals(1, 2, 2, 2, 3, 4), 50));
		else if (test == 2)
			((Problem) imp()).addCtr(new SumWeightedGE(((Problem) imp()), (Variable[]) x, vals(1, 2, 4, 5), 42));
		else if (test == 3)
			((Problem) imp()).addCtr(new CtrExtensionMDD(((Problem) imp()), (Variable[]) x, vals(2, 2, 1), range(9, 13)));

	}
}
