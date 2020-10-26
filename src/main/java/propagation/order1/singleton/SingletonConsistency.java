/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.singleton;

import propagation.order1.StrongConsistency;
import search.Solver;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import variables.Variable;

public abstract class SingletonConsistency extends StrongConsistency {

	public int nFoundSingletons;

	public SingletonConsistency(Solver solver) {
		super(solver);
	}

	/**
	 * The method to implement for performing singleton tests on the specified variable. It returns the number of removed values.
	 */
	protected abstract int makeSingletonTestsOn(Variable x);

	@Override
	protected boolean enforceStrongConsistency() {
		for (int cnt = 0; cnt < nPassesLimit; cnt++) {
			long nBefore = nEffectiveSingletonTests;
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				if (onlyNeighbours && !x.isNeighbourOf(((SolverBacktrack) solver).dr.varOfLastDecisionIf(true)))
					continue;
				if (x.dom.size() == 1) {
					nFoundSingletons++;
					continue;
				}
				int nRemovals = makeSingletonTestsOn(x);
				if (nRemovals > 0 && (x.dom.size() == 0 || enforceArcConsistencyAfterRefutation(x) == false))
					return false;
				if (solver.finished())
					return true;
			}
			if (verbose > 1)
				displayPassInfo(cnt, nEffectiveSingletonTests - nBefore, nEffectiveSingletonTests - nBefore == 0);
			if (nBefore == nEffectiveSingletonTests)
				break;
		}
		assert controlArcConsistency();
		return true;
	}

	protected final void displayPassInfo(int cnt, long nEffective, boolean lastMessage) {
		Kit.log.info("Singleton Pass " + cnt + " nEfectiveTests=" + nEffective + " nbValuesRemoved=" + Variable.nRemovedValuesFor(solver.pb.variables)
				+ (lastMessage ? "\n" : ""));
	}
}
