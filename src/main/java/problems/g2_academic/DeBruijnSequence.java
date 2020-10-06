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
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

/**
 * For base=2 and n=5, there are 2048 solutions
 */
public class DeBruijnSequence implements ProblemAPI {

	int base, n;

	@Override
	public void model() {
		int m = Utilities.power(base, n);
		int[] coeffs = valuesFrom(range(n), j -> Utilities.power(base, n - j - 1));

		Var[] x = array("x", size(m), dom(range(m)), "x[i] is the ith number (in base 10) of the sequence");
		Var[][] d = array("d", size(m, n), dom(range(base)),
				"d[i][j] is the jth digit in the base for the ith number of the sequence; d[i] is then the representation in the base of the ith number");
		Var[] g = array("g", size(base), dom(range(m + 1)), "g[i] is the number of occurrences of digit i in the first column of array d");

		allDifferent(x);
		forall(range(m), i -> sum(d[i], weightedBy(coeffs), EQ, x[i])).note("linking x and d: d[i] is the representation of x[i] in base " + base);
		forall(range(1, m + 1).range(1, n), (i, j) -> equal(d[i - 1][j], d[i % m][j - 1])).note("de Bruijn condition");
		cardinality(columnOf(d, 0), range(base), occurExactly(g));

		minimum(x, takingValue(x[0])).tag(SYMMETRY_BREAKING);
	}
}
