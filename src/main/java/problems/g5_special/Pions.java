/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g5_special;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

class Pions implements ProblemAPI {
	int n; // board size
	int p; // number of pions

	@Override
	public void model() {
		Var[] x = array("x", size(p), dom(range(n * n)));

		forall(range(p), i -> forall(range(i + 1, p), j -> conjunction(lt(dist(x[i], x[j]), p - 1), ne(x[i], x[j]))));
	}

}
