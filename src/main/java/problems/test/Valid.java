/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import java.util.Arrays;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

import utility.Kit;

public class Valid implements ProblemAPI {
	int mode, nVars, offset; // offset in 1..28

	private int[][] buildTuples() {
		int nTuples = Utilities.power(2, offset);
		int[][] t = new int[nTuples][nVars];
		for (int i = 0; i < t.length; i++)
			for (int j = 0; j < offset; j++) {
				int pow = Utilities.power(2, j);
				t[i][t[i].length - 1 - j] = (i % pow * 2 < pow ? 0 : 1);
			}
		return t;
	}

	@SuppressWarnings("unused")
	private int[][] cloneAndModifyTuples(int[][] tuples) {
		int[][] t = new int[tuples.length][nVars];
		Arrays.fill(t[0], 0);
		int limit = nVars - offset;
		for (int i = 1; i < tuples.length; i++) {
			for (int j = 0; j < limit; j++)
				t[i][j] = 1;
			for (int j = limit; j < nVars; j++)
				t[i][j] = tuples[i - 1][j];
		}
		System.out.println(Kit.join(t));
		return t;
	}

	@Override
	public void model() {
		Var[] x = array("x", size(nVars), dom(0, 1));
		if (mode == 0) {
			int[][] tuples = new int[2][nVars];
			Arrays.fill(tuples[0], 0);
			Arrays.fill(tuples[1], 1);
			extension(x, tuples);
		} else {
			int[][] tuples = new int[1][nVars];
			Arrays.fill(tuples[0], 1);
			tuples[0][0] = 0;
			extension(x, tuples);
			tuples = buildTuples();
			extension(x, tuples);
			// addConstraint(variables, cloneAndModifyTuples(tuples));
		}
	}
}
