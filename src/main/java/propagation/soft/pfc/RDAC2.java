/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.soft.pfc;

import interfaces.TagExperimental;
import search.Solver;
import search.backtrack.decomposers.Decomposer;
import search.backtrack.decomposers.Decomposer.DecomposerRDAC2;
import search.backtrack.decomposers.SolverBacktrackDecomposing;

public class RDAC2 extends RDAC implements TagExperimental {

	private Decomposer[] decomposers;

	public RDAC2(Solver solver) {
		super(solver);
		decomposers = ((SolverBacktrackDecomposing) solver).decomposers;
	}

	@Override
	protected boolean filterDomains() {
		if (!super.filterDomains())
			return false;
		int level = ((SolverBacktrackDecomposing) solver).top;
		// for (int i = 0; i <= level; i++)
		for (int i = level; i >= 0; i--)
			if (!((DecomposerRDAC2) decomposers[i]).isSatisfied())
				return false;
		return true;
	}
}
