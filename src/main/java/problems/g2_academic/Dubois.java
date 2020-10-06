/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

public class Dubois implements ProblemAPI {
	int n;

	@Override
	public void model() {
		Table table1 = table("(0,0,1)(0,1,0)(1,0,0)(1,1,1)");
		Table table2 = table("(0,0,0)(0,1,1)(1,0,1)(1,1,0)");

		Var[] x = array("x", size(3 * n), dom(0, 1));

		extension(vars(x[2 * n - 2], x[2 * n - 1], x[0]), table1);
		forall(range(n - 2), i -> extension(vars(x[i], x[2 * n + i], x[i + 1]), table1));
		forall(range(2), i -> extension(vars(x[n - 2 + i], x[3 * n - 2], x[3 * n - 1]), table1));
		forall(range(n, 2 * n - 2), i -> extension(vars(x[i], x[4 * n - 3 - i], x[i - 1]), table1));
		extension(vars(x[2 * n - 2], x[2 * n - 1], x[2 * n - 3]), table2);
	}
}