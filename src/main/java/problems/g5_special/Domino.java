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
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

/* This problem corresponds to the one described in [Zhang et Yap, 01, Making AC3 an optimal algorithm, IJCAI'01] */
public class Domino implements ProblemAPI {
	int nDominos, nValues;

	@Override
	public void model() {
		Var[] x = array("x", size(nDominos), dom(range(nValues)), "x[i] is the value of the ith domino");

		if (modelVariant("table")) {
			Table table1 = table().addFrom(range(nValues), i -> tuple(i, i));
			forall(range(nDominos - 1), i -> extension(vars(x[i], x[i + 1]), table1));

			Table table2 = table().addFrom(range(nValues), i -> tuple(i < nValues - 1 ? i + 1 : i, i));
			extension(vars(x[0], x[nDominos - 1]), table2);
		} else {
			allEqual(x);
			disjunction(eq(add(x[0], 1), x[nDominos - 1]), and(eq(x[0], x[nDominos - 1]), eq(x[0], nValues - 1))); // or eq(x[0], x[nDominos -
																													// 1],nValues - 1)
		}
	}
}
