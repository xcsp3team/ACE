/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.singleton;

import propagation.structures.forSac.QueueOfCells;
import propagation.structures.forSac.QueueOfCells.Cell;
import search.Solver;
import search.backtrack.SolverBacktrack;
import variables.Variable;

public class SAC3 extends SACGreedy {

	/**
	 * Queue used by SAC3
	 */
	protected final QueueOfCells queueOfCells;

	/**
	 * 0 = desactivated ; 1 = select last failed value (when starting a new branch) ; 2 = select last failed value + last failed variable (if last
	 * branch of size 0)
	 */
	protected final int lastConflictMode;

	public SAC3(Solver solver) {
		super(solver);
		this.queueOfCells = new QueueOfCells((SolverBacktrack) solver, true);
		this.lastConflictMode = 1; // hard coding
	}

	@Override
	protected boolean manageInconsistentValue(Variable x, int a) {
		if (!super.manageInconsistentValue(x, a))
			return false;
		if (lastConflictMode == 2)
			queueOfCells.setPriorityOf(x); // for the next branch to be built
		return true;
	}

	@Override
	protected void eraseLastBuiltBranch(int branchSize) {
		if (branchSize > 0)
			super.eraseLastBuiltBranch(branchSize);
		else
			queueOfCells.clear();
		// else is possible when queue.size > 0 with elements no more valid: some indexes of the queue may have been removed by GAC enforcment
	}

	protected final boolean buildBranch() {
		for (Cell cell = queueOfCells.pickNextCell(); cell != null; cell = queueOfCells.pickNextCell()) {
			Variable x = cell.x;
			int a = cell.a;
			nSingletonTests++;
			if (x.dom.size() == 1)
				nFoundSingletons++;
			assert !x.isAssigned() && x.dom.isPresent(a) && queue.isEmpty();
			solver.assign(x, a);
			if (enforceArcConsistencyAfterAssignment(x)) {
				if (solver.depth() == solver.pb.variables.length && stopSACWhenFoundSolution)
					solver.solManager.handleNewSolution(true);
			} else {
				solver.backtrack(x);
				int lastBuiltBranchSize = solver.depth() - nodeDepth;
				if (lastBuiltBranchSize == 0)
					return manageInconsistentValue(x, a);
				queueOfCells.add(x, a);
				if (!maximumBranchExtension || !canFindAnotherExtensionInsteadOf(x, a)) {
					if (lastConflictMode > 0)
						queueOfCells.setPriorityTo(x, a); // for the next branch to be built
					break;
				}
			}
		}
		eraseLastBuiltBranch(solver.depth() - nodeDepth);
		return true;
	}

	@Override
	protected boolean enforceStrongConsistency() {
		nodeDepth = solver.depth();
		nBranchesBuilt = sumBranchSizes = 0;
		for (int cnt = 0; cnt < nPassesLimit; cnt++) {
			long nBefore = nEffectiveSingletonTests;
			queueOfCells.fill();
			while (queueOfCells.size > 0) {
				performingProperSearch = true;
				boolean consistent = buildBranch();
				performingProperSearch = false;
				if (!consistent)
					return false;
				if (stopSACWhenFoundSolution && solver.finished())
					return true; // TODO no more compatible with solver.reset()
			}
			if (verbose > 1)
				displayPassInfo(cnt, nEffectiveSingletonTests - nBefore, nEffectiveSingletonTests - nBefore == 0);
			if (nBefore == nEffectiveSingletonTests)
				break;
		}
		assert solver.finished() || (controlArcConsistency() && controlSingletonArcConsistency());
		return true;
	}
}
