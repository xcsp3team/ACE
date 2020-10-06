/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.partial;

import interfaces.TagExperimental;
import propagation.order1.singleton.SAC;
import search.Solver;
import search.backtrack.SolverBacktrack;
import variables.Variable;
import variables.domains.Domain;

public class SACLastConflict extends SAC implements TagExperimental {

	public SACLastConflict(Solver solver) {
		super(solver);
	}

	@Override
	protected boolean enforceStrongConsistency() {
		assert solver.futVars.size() != 0;
		Variable x = ((SolverBacktrack) solver).lcReasoner.lastConflictPriorityVar();
		Domain dom = x.dom;
		if (dom.size() == 1)
			return true;
		int sizeBefore = dom.size();
		while (dom.size() > 0 && !checkSAC(x, dom.first()))
			x.dom.removeElementary(dom.first());
		int nRemovals = sizeBefore - dom.size();
		if (nRemovals > 0) {
			if (dom.size() == 0)
				return false;
			if (!super.enforceArcConsistencyAfterRefutation(x))
				return false;
		}
		return true;
	}

	@Override
	public boolean runInitially() {
		return enforceArcConsistency();
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		return enforceArcConsistencyAfterAssignment(x);
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		if (!super.enforceArcConsistencyAfterRefutation(x))
			return false;
		return enforceStrongConsistency();
	}
}
