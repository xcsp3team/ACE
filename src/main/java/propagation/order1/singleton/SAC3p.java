/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.singleton;

import java.util.stream.Stream;

import propagation.structures.forSac.Branch;
import propagation.structures.forSac.BranchExtended;
import propagation.structures.forSac.InferenceUnit;
import propagation.structures.forSac.QueueOfCells.Cell;
import search.Solver;
import variables.Domain;
import variables.Variable;

public final class SAC3p extends SAC3 {

	private final BranchExtended[] branches;

	private int nCurrentBranches;

	private BranchExtended getBranch(int i) {
		if (branches[i] == null)
			branches[i] = new BranchExtended(solver);
		return branches[i];
	}

	public SAC3p(Solver solver) {
		super(solver);
		branches = new BranchExtended[Variable.nInitValuesFor(solver.pb.variables)];
	}

	private boolean checkConsistencyOf(BranchExtended branch) {
		assert queue.isEmpty() && branch.controlModified();
		if (!branch.isModified())
			return true;
		if (branch.isInconsistent())
			return false;
		for (int i = 0; i < branch.size; i++)
			solver.assign(branch.vars[i], branch.idxs[i]);
		for (Variable x : solver.pb.variables) {
			if (x.isAssigned())
				continue;
			assert !(branch.has(x));
			InferenceUnit inferenceUnit = branch.inferenceUnits[x.num];
			Domain dom = x.dom;
			for (int a = dom.first(); a != -1; a = dom.next(a))
				if (inferenceUnit.absents[a])
					x.dom.removeElementary(a);
			if (dom.size() == 0) {
				for (int cnt = 0; cnt < branch.size; cnt++)
					solver.backtrack();
				return false;
			}
			if (inferenceUnit.modified)
				queue.add(x);
		}
		assert queue.size() > 0;
		boolean consistent = propagate();
		if (consistent)
			branch.recordProblemDomain();
		for (int cnt = 0; cnt < branch.size; cnt++)
			solver.backtrack();
		return consistent;
	}

	private void updateBranchesAfterRemovalOf(Variable x, int a) {
		for (int i = 0; i < nCurrentBranches; i++)
			branches[i].updateAfterRemovalOf(x, a);
	}

	private void updateQueueFromInconsistentBranches() {
		for (int i = 0; i < nCurrentBranches; i++) {
			BranchExtended branch = branches[i];
			if (checkConsistencyOf(branch) == false) {
				for (int j = 0; j < branch.size; j++)
					queueOfCells.add(branch.vars[j], branch.idxs[j]);
				branches[i] = branches[nCurrentBranches - 1];
				branches[nCurrentBranches - 1] = branch; // swap to avoid loosing memory
				branch.clear();
				nCurrentBranches--;
				i--;
			}
			// else { System.out.println("Kept Branch"); branch.display(); }
		}
	}

	protected boolean reestablishAC(Variable x) {
		for (Variable y : solver.pb.variables)
			y.dom.setMark();
		if (super.enforceArcConsistencyAfterRefutation(x) == false)
			return false;
		for (Variable y : solver.pb.variables) {
			int mark = y.dom.indexAtMark();
			for (int a = y.dom.lastRemoved(); a != mark; a = y.dom.prevRemoved(a))
				updateBranchesAfterRemovalOf(y, a);
		}
		return true;
	}

	@Override
	protected boolean manageInconsistentValue(Variable x, int a) {
		nEffectiveSingletonTests++;
		x.dom.removeElementary(a);
		if (shavingEvaluator != null)
			shavingEvaluator.updateRatioAfterShavingSuccess(x);
		if (x.dom.size() == 0)
			return false;
		updateBranchesAfterRemovalOf(x, a);
		if (!reestablishAC(x))
			return false;
		if (lastConflictMode == 2)
			queueOfCells.setPriorityOf(x); // for the next branch to be built
		return true;
	}

	protected void eraseLastBuiltBranch(Branch branch) {
		if (branch.size > 0) {
			nCurrentBranches++;
			((BranchExtended) branch).recordProblemDomain();
		}
		super.eraseLastBuiltBranch(branch.size);
	}

	protected boolean buildBranch(Branch branch) {
		branch.clear();
		for (Cell cell = queueOfCells.pickNextCell(); cell != null; cell = queueOfCells.pickNextCell()) {
			Variable x = cell.x;
			int a = cell.a;
			if (x.dom.size() == 1)
				nFoundSingletons++;
			assert !x.isAssigned() && x.dom.isPresent(a) && queue.isEmpty();
			nSingletonTests++;
			solver.assign(x, a);
			if (enforceArcConsistencyAfterAssignment(x)) {
				branch.add(x, a);
				if (solver.depth() == solver.pb.variables.length && stopSACWhenFoundSolution)
					solver.solManager.handleNewSolution(true);
			} else {
				solver.backtrack(x);
				if (branch.size == 0)
					return manageInconsistentValue(x, a);
				queueOfCells.add(x, a);
				if (!maximumBranchExtension) {
					if (lastConflictMode > 0)
						queueOfCells.setPriorityTo(x, a); // for the next branch to be built
					break;
				}
			}
		}
		eraseLastBuiltBranch(branch);
		return true;
	}

	@Override
	protected boolean enforceStrongConsistency() {
		nBranchesBuilt = sumBranchSizes = nCurrentBranches = 0;
		queueOfCells.fill();
		while (queueOfCells.size > 0) {
			while (queueOfCells.size > 0) {
				assert controlBranches();
				if (buildBranch(getBranch(nCurrentBranches)) == false)
					return false;
				if (stopSACWhenFoundSolution && solver.finished())
					return true;
			}
			updateQueueFromInconsistentBranches();
		}
		assert controlArcConsistency() && controlSingletonArcConsistency();
		return true;
	}

	/**
	 * Control method : return true iff there is non inconsistency between branches and the queue
	 * 
	 * @return
	 */
	private boolean controlBranches() {
		return Stream.of(branches).allMatch(b -> b.controlWrt(queueOfCells));
	}
}
