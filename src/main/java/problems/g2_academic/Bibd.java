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

public class Bibd implements ProblemAPI {

	int v, b, r, k, l; // l stands for lambda

	@Override
	public void model() {
		if (b == 0)
			b = (l * v * (v - 1)) / (k * (k - 1)); // when b is 0, we compute it
		if (r == 0)
			r = (l * (v - 1)) / (k - 1); // when r is 0, we compute it

		Var[][] x = array("x", size(v, b), dom(0, 1), "x[i][j] is the value of the matrix at row i and column j");

		forall(range(v), i -> sum(x[i], EQ, r)).note("constraints on rows");
		forall(range(b), j -> sum(columnOf(x, j), EQ, k)).note("constraints on columns");

		if (modelVariant(""))
			forall(range(v), i -> forall(range(i + 1, v), j -> sum(x[i], weightedBy(x[j]), EQ, l))).note("scalar constraints with respect to lambda");

		if (modelVariant("aux")) {
			Var[][][] s = array("s", size(v, v, b), (i, j, k) -> dom(0, 1).when(i < j), "s[i][j][k] is the product of x[i][k] and x[j][k]");
			forall(range(v), i -> forall(range(i + 1, v).range(b), (j, k) -> equal(s[i][j][k], mul(x[i][k], x[j][k])))).note("computing scalar variables");
			forall(range(v), i -> forall(range(i + 1, v), j -> sum(s[i][j], EQ, l))).note("scalar constraints with respect to lambda");
		}

		lexMatrix(x, INCREASING).tag(SYMMETRY_BREAKING).note("Increasingly ordering both rows and columns");
	}
}
