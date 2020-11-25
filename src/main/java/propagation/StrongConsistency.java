/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation;

import solver.Solver;
import utility.Kit;
import variables.Variable;

public abstract class StrongConsistency extends GAC {

	protected int nPassesLimit = Integer.MAX_VALUE; // TODO hard coding
	protected boolean onlyBounds, onlyNeighbours; // TODO hard coding

	protected final int verbose;

	public StrongConsistency(Solver solver) {
		super(solver);
		this.verbose = solver.head.control.general.verbose;
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
		int nBefore = solver.problem.nValuesRemoved;
		if (enforceArcConsistency() == false)
			return false;
		if (settings.strongOnlyWhenACEffective && solver.problem.nValuesRemoved == nBefore)
			return true;
		return enforceMore();
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		int nBefore = solver.problem.nValuesRemoved;
		if (enforceArcConsistencyAfterAssignment(x) == false)
			return false;
		if (performingProperSearch || settings.strongOnlyAtPreprocessing || (settings.strongOnlyWhenACEffective && solver.problem.nValuesRemoved == nBefore)
				|| (settings.strongOnlyWhenNotSingleton && !x.dom.isModifiedAtCurrentDepth() && hasSolverPropagatedAfterLastButOneDecision()))
			return true;
		return enforceMore();
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		int nBefore = solver.problem.nValuesRemoved;
		if (enforceArcConsistencyAfterRefutation(x) == false)
			return false;
		if (performingProperSearch || settings.strongOnlyAtPreprocessing || (settings.strongOnlyWhenACEffective && solver.problem.nValuesRemoved == nBefore))
			return true;
		return enforceMore();
	}

}
