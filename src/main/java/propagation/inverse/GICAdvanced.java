/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.inverse;

import search.Solver;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public abstract class GICAdvanced extends GIC1 {

	protected int[] nValuesToBeSupported; // ID = variable position

	protected int nSupVariables;

	protected int[] supVariableNums; // nums of the variables for which gic must be checked

	protected int cursor; // global variable used by some methods

	public GICAdvanced(Solver solver) {
		super(solver);
		nValuesToBeSupported = new int[solver.pb.variables.length];
		supVariableNums = new int[solver.pb.variables.length];
	}

	protected abstract void intializationAdvanced();

	protected abstract boolean isInverseAdvanced(Variable x, int a);

	@Override
	public boolean enforceStrongConsistency() {
		intializationAdvanced();
		long nSolutionsBefore = before();
		int nValuesRemoved = 0;
		for (cursor = nSupVariables - 1; cursor >= 0; cursor--) {
			Variable x = solver.pb.variables[supVariableNums[cursor]];
			if (nValuesToBeSupported[x.num] == 0)
				continue;
			Domain dom = x.dom;
			for (int a = dom.first(); a != -1; a = dom.next(a))
				if (!isInverseAdvanced(x, a)) {
					x.dom.removeElementary(a);
					nValuesRemoved++;
				}
			Kit.control(dom.size() != 0, () -> "Not possible to reach inconsistency with GIC (or your instance is unsat)");
		}
		after(nSolutionsBefore, nValuesRemoved);
		return true;
	}
}
