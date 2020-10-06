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
import org.xcsp.modeler.api.ProblemAPI;

public class Egdr implements ProblemAPI {
	int d, r;

	private int[] next(int[] tuple) {
		for (int i = tuple.length - 1; i >= 1; i--)
			if (tuple[i] == 0) {
				tuple[i] = 1;
				return tuple;
			} else
				tuple[i] = 0;
		return null;
	}

	private int[][] buildTuples() {
		int[][] tuples = new int[(int) Math.pow(2, r - 1) + d - 2][];
		int i = 0;
		int[] tuple = new int[r];
		while (tuple != null) {
			tuples[i++] = tuple.clone();
			tuple = next(tuple);
		}
		tuple = new int[r];
		for (int j = 2; j < d; j++) {
			Arrays.fill(tuple, j);
			tuples[i++] = tuple.clone();
		}
		return tuples;
	}

	@Override
	public void model() {
		Var[] x = array("x", size(r), dom(range(d)));
		extension(x, buildTuples());
	}
}
