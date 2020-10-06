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

public class Enigme5 implements ProblemAPI {

	int limit, value; // try with 364 and 55440

	private int nDecompositions(int limit, int value, int[][] decs) {
		int cnt = 0;
		// Arrays.fill(nbOccurrences, 0);
		for (int i = 1; i <= limit; i++) {
			int ub = i * (limit) * (limit - 1) * (limit - 2);
			if (ub < value)
				continue;
			int lb = i * (i + 1) * (i + 2) * (i + 3);
			if (lb > value)
				break;
			for (int j = i + 1; j <= limit; j++) {
				ub = i * j * (limit) * (limit - 1);
				if (ub < value)
					continue;
				lb = i * j * (j + 1) * (j + 2);
				if (lb > value)
					break;
				for (int k = j + 1; k <= limit; k++) {
					ub = i * j * k * (limit);
					if (ub < value)
						continue;
					lb = i * j * k * (k + 1);
					if (lb > value)
						break;
					for (int l = k + 1; l <= limit; l++) {
						if (i * j * k * l > value)
							break;
						if (i * j * k * l == value) {
							if (decs == null) {
								// nbOccurrences[i]++; nbOccurrences[j]++; nbOccurrences[k]++; nbOccurrences[l]++;
							} else
								decs[cnt] = new int[] { i, j, k, l };
							cnt++;
						}
					}
				}
			}
		}
		return cnt;
	}

	private int[][] buildPermutations() {
		int[][] decs = new int[nDecompositions(limit, value, null)][];
		nDecompositions(limit, value, decs);
		int[][] tuples = new int[decs.length * 24][];
		int cnt = 0;
		for (int[] dec : decs)
			for (int i = 0; i < 4; i++)
				for (int j = 0; j < 4; j++)
					if (i != j)
						for (int k = 0; k < 4; k++)
							if (k != i && k != j)
								for (int l = 0; l < 4; l++)
									if (l != i && l != j && l != k)
										tuples[cnt++] = tuple(dec[i], dec[j], dec[k], dec[l]);
		return tuples;
	}

	@Override
	public void model() {
		int[][] table = buildPermutations();

		Var[] x = array("x", size(4 * 4 * 4), dom(range(1, limit + 1))); // oder 4

		allDifferent(x);
		// row constraints
		forall(range(16), i -> extension(vars(x[i * 4], x[i * 4 + 1], x[i * 4 + 2], x[i * 4 + 3]), table));
		// column constraints
		forall(range(4), i -> extension(vars(x[i], x[i + 4], x[i + 8], x[i + 12]), table));
		forall(range(16, 20), i -> extension(vars(x[i], x[i + 4], x[i + 8], x[i + 12]), table));
		forall(range(32, 36), i -> extension(vars(x[i], x[i + 4], x[i + 8], x[i + 12]), table));
		forall(range(48, 52), i -> extension(vars(x[i], x[i + 4], x[i + 8], x[i + 12]), table));
		// top constraints
		forall(range(16), i -> extension(vars(x[i], x[i + 16], x[i + 32], x[i + 48]), table));
		// diagonal constraints
		extension(vars(x[0], x[21], x[42], x[63]), table);
		extension(vars(x[15], x[26], x[37], x[48]), table);
		extension(vars(x[3], x[22], x[41], x[60]), table);
		extension(vars(x[12], x[25], x[38], x[51]), table);
	}
}
