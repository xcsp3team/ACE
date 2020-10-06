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
import org.xcsp.modeler.api.ProblemAPI;

public class Opd implements ProblemAPI {
	int v, b, r;

	private int lb() {
		int rv = r * v, rvmodb = rv % b, floorrv = rv / b, ceilrv = rv / b + (rv % b != 0 ? 1 : 0);
		int num = (ceilrv * ceilrv * rvmodb + floorrv * floorrv * (b - rvmodb) - rv), den = v * (v - 1);
		return num / den + (num % den != 0 ? 1 : 0);
	}

	@Override
	public void model() {

		Var z = var("z", dom(rangeClosed(lb(), b)), "objective variable");
		Var[][] x = array("x", size(v, b), dom(0, 1), "x[i][j] is the value at row i and column j");

		forall(range(v), i -> sum(x[i], EQ, r));

		if (modelVariant(""))
			forall(range(v), i -> forall(range(i + 1, v), j -> sum(x[i], x[j], LE, z)));

		if (modelVariant("aux")) {
			Var[][][] s = array("s", size(v, v, b), (i, j, k) -> dom(0, 1).when(i < j), "scalar variables");
			forall(range(v), i -> forall(range(i + 1, v).range(b), (j, k) -> equal(s[i][j][k], mul(x[i][k], x[j][k]))));
			forall(range(v), i -> forall(range(i + 1, v), j -> sum(s[i][j], LE, z))).note("at most lambda");
		}

		lexMatrix(x, INCREASING).tag(SYMMETRY_BREAKING);

		minimize(z);
	}
}
