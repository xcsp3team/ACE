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

public class PropStress implements ProblemAPI {
	int n;

	@Override
	public void model() {
		int k = n, m = n; // k : Number of times round the loop ; m : m^2 propagators per change of loop ; n : Number of iterations of
							// change per loop

		Var[] x = array("x", size(m + 1), dom(range(k * n + 1)));
		Var[] y = array("y", size(n + 1), dom(range(k * n + 1)));

		forall(rangeClosed(2, n), i -> lessEqual(sub(y[i - 1], y[i]), 0));
		forall(rangeClosed(1, n), i -> lessEqual(sub(y[0], y[i]), n - i + 1));
		lessEqual(sub(y[n], x[0]), 0);
		forall(range(m + 1), i -> forall(range(i + 1, m + 1), j -> lessEqual(sub(x[i], x[j]), 0)));
		lessEqual(sub(x[m], y[0]), -2);
	}
}
