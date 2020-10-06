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
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

/*
 * 432 solutions for order 5 (with symmetry breaking); no solution for order 6
 */
public class Ortholatin implements ProblemAPI {
	int n;

	@Override
	public void model() {
		Var[][] x = array("x", size(n, n), dom(range(n)), "x is the first Latin square");
		Var[][] y = array("y", size(n, n), dom(range(n)), "y is the second Latin square");
		Var[] z = array("z", size(n * n), dom(range(n * n)), "z is the matrix used to control orthogonality");

		allDifferentMatrix(x).note("ensuring that x is a Latin square");
		allDifferentMatrix(y).note("ensuring that y is a Latin square");
		allDifferent(z).note("ensuring orthogonality of x and y through z");

		Table table = table().addFrom(range(n).range(n), (i, j) -> tuple(i, j, i * n + j));
		forall(range(n).range(n), (i, j) -> extension(vars(x[i][j], y[i][j], z[i * n + j]), table)).note("computing z from x and y");

		instantiation(x[0], range(n)).tag(SYMMETRY_BREAKING);
		instantiation(y[0], range(n)).tag(SYMMETRY_BREAKING);
	}
}
