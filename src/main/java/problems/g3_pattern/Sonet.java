/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

// See "Automatically Improving Constraint Models in Savile Row"

public class Sonet implements ProblemAPI {

	int m, n, r;
	int[][] connections;

	@Override
	public void model() {
		int nConnections = connections.length;

		Var[][] x = array("x", size(m, n), dom(0, 1), "x[i][j] is 1 if the ith ring contains the jth node");

		Table table = table().addFrom(range(m), i -> range(2 * m).map(j -> j / 2 == i ? 1 : STAR));
		forall(range(nConnections), c -> extension(variablesFrom(range(m), i -> vars(x[i][connections[c][0]], x[i][connections[c][1]])), table));
		forall(range(m), i -> atMost(x[i], takingValue(1), r));
		increasing(x);

		minimize(SUM, x);

	}
}
