/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.partial;

import heuristics.variables.HeuristicVariables;
import interfaces.TagExperimental;
import propagation.order1.singleton.SAC;
import search.Solver;
import search.backtrack.SolverBacktrack;
import variables.Variable;

public class SACSelectedVariable extends SAC implements TagExperimental {

	public SACSelectedVariable(Solver solver) {
		super(solver);
	}

	@Override
	protected boolean enforceStrongConsistency() {
		HeuristicVariables voh = ((SolverBacktrack) (solver)).heuristicVars;
		boolean modified = true;
		while (modified) {
			modified = false;
			Variable x = voh.bestVar();
			int nRemovals = makeSingletonTestsOn(x);
			// System.out.println("nbremovals " + nbRemovals);
			if (nRemovals > 0) {
				if (x.dom.size() == 0)
					return false;
				modified = true;
				if (!super.enforceArcConsistencyAfterRefutation(x))
					return false;
			}
			if (solver.finished())
				return true;
		}
		assert controlArcConsistency() && controlSingletonArcConsistency();
		return true;
	}
}
