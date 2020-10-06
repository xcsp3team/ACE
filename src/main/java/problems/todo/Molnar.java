/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.todo;

import java.util.stream.Stream;

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.predicates.XNode;
import org.xcsp.modeler.api.ProblemAPI;

//See "Automatically Improving Constraint Models in Savile Row"

public class Molnar implements ProblemAPI {

	int k, d;

	@Override
	public void model() {
		Var[][] x = array("x", size(k, k), dom(vals(rangeClosed(-d, -2), 0, rangeClosed(2, d))), "x[i][j] is the value of the matrix at row i and column j");
		Var det = var("det", dom(-1, 1));

		if (k == 3) {
			Stream<XNode<IVar>> list = Stream.of(mul(x[0][0], x[1][1], x[2][2]), mul(x[0][0], x[1][2], x[2][1]), mul(x[0][1], x[1][2], x[2][0]),
					mul(x[0][1], x[1][0], x[2][2]), mul(x[0][2], x[1][0], x[2][1]), mul(x[0][2], x[1][1], x[2][0]));
			sum(list, weightedBy(1, -1, 1, -1, 1, -1), EQ, det);
			// TO BE continued
		}

		lexMatrix(x, INCREASING).tag(SYMMETRY_BREAKING).note("Increasingly ordering both rows and columns");
	}
}
