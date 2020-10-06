/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

// Pb045 in CSPLib
public class CoveringArray implements ProblemAPI {
	int t, k, g, b;

	private Table buildTable() {
		int[][] combinations = allCombinations(k, t);
		return table().add(Stream.of(allCartesian(g, k)).map(t -> Stream.of(combinations).mapToInt(c -> {
			int res = 0, coeff = 1;
			for (int i = c.length - 1; i >= 0; i--) {
				res += t[c[i]] * coeff;
				coeff *= g;
			}
			return res;
		}).toArray()));
	}

	@Override
	public void model() {
		int nCombinations = Utilities.binomial(k, t), nValues = Utilities.power(g, t);

		Var[][] p = array("p", size(nCombinations, nValues), dom(range(b)));
		Var[][] v = array("v", size(nCombinations, b), dom(range(nValues))); // add value bot later?

		forall(range(nCombinations), i -> allDifferent(p[i]));
		forall(range(nCombinations), i -> channel(p[i], v[i]));

		Table table = buildTable();
		forall(range(b), j -> extension(columnOf(v, j), table));
	}
}
