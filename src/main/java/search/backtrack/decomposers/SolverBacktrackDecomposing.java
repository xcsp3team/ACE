/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search.backtrack.decomposers;

import executables.Resolution;
import interfaces.TagExperimental;
import search.backtrack.SolverBacktrack;
import search.backtrack.decomposers.Decomposer.DecomposerRDAC2;
import utility.Reflector;
import variables.Variable;

public final class SolverBacktrackDecomposing extends SolverBacktrack implements TagExperimental {

	public Decomposer[] decomposers;

	public int top = -1;

	public void setDomainsMarks(int level) {
		for (Variable x : pb.variables)
			x.dom.setMark(level);
	}

	public void restoreDomainsAtMarks(int level) {
		for (Variable x : pb.variables)
			x.dom.restoreAtMark(level);
	}

	public void pushVariable(Variable var) {}

	@Override
	protected void manageEmptyDomainBeforeBacktracking() {
		stats.nBacktracks++;
	}

	public SolverBacktrackDecomposing(Resolution resolution) {
		super(resolution);
		this.decomposers = new Decomposer[Variable.nValidValuesFor(resolution.problem.variables) + 1];
	}

	private void branchingFor(Variable x) {
		top++;
		if (decomposers[top] == null)
			decomposers[top] = Reflector.buildObject(rs.cp.settingHardCoding.classForDecompositionSolver, Decomposer.class, this);
		Decomposer decomposer = decomposers[top];
		decomposer.initialize(x);
		int a = x.heuristicVal.bestIndex();
		assert !(decomposer instanceof DecomposerRDAC2) || x.dom.size() == 1 || a == ((DecomposerRDAC2) decomposer).getIndex();
		if (tryAssignment(x, a))
			explore();
		backtrack(x);
		if (!finished() && !restarter.currRunFinished() && tryRefutation(x, a)) {
			decomposer.split();
			if (decomposer.getNbPieces() == 1)
				explore();
			else {
				setDomainsMarks(top);
				for (int num = 0; num < decomposer.getNbPieces(); num++) {
					int res = decomposer.buildPiece(num);
					if (res == -1)
						break;
					if (res == 1)
						explore();
					if (num < decomposer.getNbPieces() - 1)
						restoreDomainsAtMarks(top);
				}
			}
		}
		top--;
	}

	// private int[] solscenw_7_sub0_ext = { 16, 33, 40, 0, 22, 32, 14, 32, 26, 31, 35, 0, 25, 20, 19, 11 };
	// private int[] solRoot3 = { 11, 33, 11, 22, 27, 33, 38, 22, 18, 16, 11 };

	@Override
	public void explore() {
		if (futVars.size() == 0)
			solManager.handleNewSolutionAndPossiblyOptimizeIt();
		else if (!finished() && !restarter.currRunFinished())
			branchingFor(heuristicVars.bestVar());
	}
}