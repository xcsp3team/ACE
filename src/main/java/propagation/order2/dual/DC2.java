/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order2.dual;

import search.Solver;
import variables.Variable;

public final class DC2 extends DC2Abstract {

	public DC2(Solver solver) {
		super(solver);
	}

	@Override
	protected boolean removeAdditionalTuples(Variable x, int a, Variable y) {
		return isMarkLastDropped(y.dom) ? false : removeTuplesFrom(x, a, solver.pb.addUniversalConstraintDynamicallyBetween(x, y));
	}
}
