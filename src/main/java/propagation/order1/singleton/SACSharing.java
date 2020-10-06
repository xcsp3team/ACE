/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.singleton;

import org.xcsp.common.Types.TypeOptimization;

import propagation.structures.forSac.Inferrer;
import search.Solver;
import variables.Variable;
import variables.domains.Domain;

public abstract class SACSharing extends SAC {

	protected Inferrer inferenceManager;

	protected abstract void buildInferenceManager();

	public SACSharing(Solver solver) {
		super(solver);
		buildInferenceManager();
	}

	protected final boolean checkSAC(Variable x, int a, TypeOptimization currentOpt) {
		nSingletonTests++;
		solver.assign(x, a);
		boolean consistent = inferenceManager.exploitInferences(x, a);
		if (consistent) {
			consistent = propagate();
			if (consistent)
				inferenceManager.updateInferences(x, a);
			else
				nEffectiveSingletonTests++;
		}
		assert (!consistent || controlArcConsistency()) : "problem after singleton test: " + x + " = " + a;
		solver.backtrack(x);
		return consistent;
	}

	@Override
	protected final int makeSingletonTestsOn(Variable x) {
		int sizeBefore = x.dom.size();
		Domain dom = x.dom;
		if (onlyBounds) {
			while (dom.size() > 0 && checkSAC(x, dom.first(), TypeOptimization.MINIMIZE) == false)
				dom.removeElementary(dom.first());
			while (dom.size() > 1 && checkSAC(x, dom.last(), TypeOptimization.MAXIMIZE) == false)
				dom.removeElementary(dom.last());
		} else
			for (int a = dom.first(); a != -1; a = dom.next(a))
				if (checkSAC(x, a, null) == false)
					dom.removeElementary(a);
		return (sizeBefore - x.dom.size());
	}

	/**
	 * Currently, this kind of SAC cannot be maintained during search.
	 */
	@Override
	public final boolean runAfterAssignment(Variable x) {
		return enforceArcConsistencyAfterAssignment(x);
	}

	/**
	 * Currently, this kind of SAC cannot be maintained during search.
	 */
	@Override
	public final boolean runAfterRefutation(Variable x) {
		return enforceArcConsistencyAfterRefutation(x);
	}
}
