/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.order1;

import search.Solver;
import utility.Kit;
import variables.Variable;

public abstract class StrongConsistency extends AC {

	protected int nPassesLimit = Integer.MAX_VALUE; // TODO hard coding
	protected boolean onlyBounds, onlyNeighbours; // TODO hard coding

	public StrongConsistency(Solver solver) {
		super(solver);
		Kit.control(solver.observersSearch == null || solver.observersSearch.size() == 0);
	}

	/**
	 * Performs strong inference. The method to implement for each subclass of Strong.
	 */
	protected abstract boolean enforceStrongConsistency();

	protected boolean enforceMore() {
		solver.stats.store();
		boolean consistent = enforceStrongConsistency();
		solver.stats.restore();
		return consistent;
	}

	@Override
	public boolean runInitially() {
		int nBefore = pb().nValuesRemoved;
		if (enforceArcConsistency() == false)
			return false;
		if (cp().settingPropagation.strongOnlyWhenACEffective && pb().nValuesRemoved == nBefore)
			return true;
		return enforceMore();
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		int nBefore = pb().nValuesRemoved;
		if (enforceArcConsistencyAfterAssignment(x) == false)
			return false;
		return performingProperSearch || cp().settingPropagation.strongOnlyAtPreprocessing
				|| (cp().settingPropagation.strongOnlyWhenACEffective && pb().nValuesRemoved == nBefore)
				|| (cp().settingPropagation.strongOnlyWhenNotSingleton && !x.dom.isModifiedAtCurrentDepth() && hasSolverPropagatedAfterLastButOneDecision()) ? true
						: enforceMore();
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		int nBefore = pb().nValuesRemoved;
		if (enforceArcConsistencyAfterRefutation(x) == false)
			return false;
		return performingProperSearch || cp().settingPropagation.strongOnlyAtPreprocessing
				|| (cp().settingPropagation.strongOnlyWhenACEffective && pb().nValuesRemoved == nBefore) ? true : enforceMore();
	}

}
