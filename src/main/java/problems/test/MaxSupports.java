/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

import tools.random.RandomGeneration.RandomGenerationProp;
import tools.random.RandomGeneration.RandomGenerationProp.TypeList;

public class MaxSupports implements ProblemAPI {
	int n, d, e;

	@Override
	public void model() {
		int[][] tuples = IntStream.range(0, 2 * d - 1).mapToObj(i -> i < d - 1 ? tuple(i, d - 1) : tuple(d - 1, i - d + 1)).toArray(int[][]::new);
		int[][] scopes = new RandomGenerationProp(n, 2, 0).selectSets(e, TypeList.UNSTRUCTURED, false);

		Var[] x = array("x", size(n), dom(range(d)));
		forall(range(e), i -> extension(vars(x[scopes[i][0]], x[scopes[i][1]]), tuples));
	}
}
