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

import utility.Kit;

// Problem of cliques of AllDiff defined at Page 6 of [Global Constraints: a survey, JC Regin]
public class CliquesJC implements ProblemAPI {
	int n;

	private int[][] buildCliquesSignatures() {
		int[][] m = new int[n + 1][n];
		m[0] = Kit.range(n);
		int max = n - 1;
		for (int i = 1; i <= n; i++) {
			for (int j = 0; j < i; j++)
				m[i][j] = m[j][i - 1];
			for (int j = i; j < n; j++)
				m[i][j] = ++max;
		}
		return m;
	}

	@Override
	public void model() {
		control(n % 2 == 0, "the order must be odd");
		int[][] m = buildCliquesSignatures();

		Var[] x = array("x", size((n * (n + 1)) / 2), dom(range(n)));
		forall(range(n + 1), i -> allDifferent(select(x, m[i])));
	}
}
