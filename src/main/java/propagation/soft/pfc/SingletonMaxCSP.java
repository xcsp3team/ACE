/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.soft.pfc;

import interfaces.TagExperimental;
import search.Solver;
import variables.Variable;
import variables.domains.Domain;

public class SingletonMaxCSP extends PRDAC implements TagExperimental {

	int nbSingletonTests, nbEffectiveSingletonTests;

	protected boolean increment;

	public SingletonMaxCSP(Solver solver) {
		super(solver);
	}

	protected boolean singletonTest(Variable x, int a) {
		nbSingletonTests++;
		solver.assign(x, a);
		boolean consistent = super.runAfterAssignment(x);
		if (!consistent)
			nbEffectiveSingletonTests++;
		solver.backtrack(x);
		// supportManager.restoreSupportsOfFutureVariables(solver.getCurrentDepth());
		return consistent;
	}

	private int filteringBySACOf(Variable x) {
		Domain dom = x.dom;
		int sizeBefore = dom.size();
		int a = dom.first();
		while (a != -1) {
			int b = dom.next(a); // next index to be saved
			if (!singletonTest(x, a))
				x.dom.removeElementary(a);
			a = b;
		}
		return sizeBefore - dom.size();
	}

	protected boolean filterBySAC() {
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			// if (!varf.isNeighbourOf(lastVariable)) continue;
			int nbRemovals = filteringBySACOf(x);
			if (nbRemovals > 0) {
				// System.out.println("nb Removals = " + nbRemovals);
				if (x.dom.size() == 0) {
					// varf.incrementWeightedDegree();
					return false;
				}
				// if (!super.checkConsistencyAfterRefutationOf(varf, solver.getCurrentDepth() + 1))
				// return false;
			}
		}
		return super.runAfterRefutation(null);
	}

	@Override
	public boolean runInitially() {
		increment = true;
		if (!super.runInitially())
			return false;
		increment = false;
		return filterBySAC();
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		increment = true;
		if (!super.runAfterAssignment(x))
			return false;
		increment = false;
		return filterBySAC();

	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		increment = true;
		if (!super.runAfterRefutation(x))
			return false;
		// return true;
		increment = false;
		return filterBySAC();
	}

}
