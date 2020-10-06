/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import java.util.ArrayList;
import java.util.List;

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.predicates.XNode;
import org.xcsp.modeler.api.ProblemAPI;

/**
 * A ruler of a specified length must contain a specified number of marks. See http://4c.ucc.ie/~tw/csplib/prob/prob006/index.html
 */
public class GolombRuler implements ProblemAPI {
	int n;

	private List<XNode<IVar>> trees(Var[] x) {
		List<XNode<IVar>> list = new ArrayList<>();
		for (int i = 0; i < x.length; i++)
			for (int j = i + 1; j < x.length; j++)
				list.add(abs(sub(x[i], x[j])));
		return list;
	}

	@Override
	public void model() {
		int rulerLength = n * n + 1; // a trivial upper-bound of an optimal ruler length

		Var[] x = array("x", size(n), dom(range(rulerLength)), "x[i] is the position of the ith tick");

		if (modelVariant(""))
			allDifferent(trees(x).stream()).note("all distances are different");
		else if (modelVariant("dec"))
			forall(range(n).range(n).range(n).range(n), (i, j, k, l) -> {
				if (i < j && i < k && k < l)
					different(dist(x[i], x[j]), dist(x[k], x[l]));
			}).note("all distances are different");
		else if (modelVariant("aux")) {
			Var[][] y = array("y", size(n, n), (i, j) -> dom(range(1, rulerLength)).when(i < j),
					"y[i][j] is the distance between x[i] and x[j], for i strictly less than j");

			allDifferent(y).note("all distances are different");
			forall(range(n), i -> forall(range(i + 1, n), j -> equal(x[j], add(x[i], y[i][j])))).note("linking variables from both arrays");

			decisionVariables(x);
		}

		block(() -> {
			equal(x[0], 0);
			strictlyIncreasing(x);
		}).tag(SYMMETRY_BREAKING);

		minimize(MAXIMUM, x).note("minimizing the position of the rightmost tick");
		// minimize(x[n - 1]).note("minimizing the position of the rightmost tick") is possible if strictlyIncreasing(x) is posted
	}
}
