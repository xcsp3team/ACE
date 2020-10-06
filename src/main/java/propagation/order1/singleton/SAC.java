/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.singleton;

import search.Solver;
import utility.Kit;
import variables.Variable;

public abstract class SAC extends SingletonConsistency {

	public SAC(Solver solver) {
		super(solver);
	}

	/**
	 * Returns true iff (x,a) is SAC.
	 */
	protected boolean checkSAC(Variable x, int a) {
		// System.out.println("trying" + x + " " + a);
		solver.assign(x, a);
		boolean consistent = enforceArcConsistencyAfterAssignment(x);
		// System.out.println("consistent trying" + x + " " + a + " " + consistent);
		solver.backtrack(x);
		nSingletonTests++;
		if (!consistent)
			nEffectiveSingletonTests++;
		return consistent;
	}

	@Override
	protected int makeSingletonTestsOn(Variable x) {
		int sizeBefore = x.dom.size();
		if (onlyBounds) {
			while (x.dom.size() > 0 && checkSAC(x, x.dom.first()) == false)
				x.dom.removeElementary(x.dom.first());
			while (x.dom.size() > 1 && checkSAC(x, x.dom.last()) == false)
				x.dom.removeElementary(x.dom.last());
		} else
			for (int a = x.dom.first(); a != -1; a = x.dom.next(a))
				if (checkSAC(x, a) == false)
					x.dom.removeElementary(a);
		return sizeBefore - x.dom.size();
	}

	/**
	 * Control method : returns true iff (x,a) is SAC.
	 */
	private boolean controlSingleton(Variable x, int a) {
		solver.assign(x, a);
		boolean consistent = enforceArcConsistencyAfterAssignment(x);
		solver.backtrack(x);
		if (!consistent)
			Kit.log.warning(x + " " + a + " not singleton consistent");
		return consistent;
	}

	/**
	 * Control method : returns true iff the CN is SAC.
	 */
	protected final boolean controlSingletonArcConsistency() {
		if (nPassesLimit == Integer.MAX_VALUE)
			return true;
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x))
			for (int a = x.dom.first(); a != -1; a = x.dom.next(a))
				if (controlSingleton(x, a) == false)
					return false;
		return true;
	}

}
