/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.soft.pfc;

import heuristics.variables.HeuristicVariables.BestScoredVariable;
import interfaces.TagExperimental;
import propagation.structures.forSac.Branch;
import search.Solver;
import utility.CombinatorOfTwoInts;
import variables.Variable;

public class SingletonMaxCSP3Single extends PRDAC implements TagExperimental {
	private Branch branch;

	private boolean maximumBranchExtension = false; // hard coding

	int nbSingletonTests, nbEffectiveSingletonTests;

	protected int nbBuiltBranches;

	protected int cumulBranchSizes;

	private int nbUntestedVariables;

	private boolean[] untestedVariables;

	private Variable lastFailedVariable;

	private int lastFailedIndex;

	protected boolean increment;

	protected BestScoredVariable bestScoredVariable = new BestScoredVariable();

	private CombinatorOfTwoInts combinator;

	private void setUntested(int position, boolean b) {
		if (untestedVariables[position] != b) {
			untestedVariables[position] = b;
			nbUntestedVariables = nbUntestedVariables + (b ? 1 : -1);
		}
		assert controlUntested();
	}

	private void initializeSingleton() {
		Variable[] variables = solver.pb.variables;
		for (int i = 0; i < untestedVariables.length; i++)
			untestedVariables[i] = variables[i].isFuture();
		nbUntestedVariables = solver.futVars.size();
		lastFailedVariable = null;
		assert controlUntested();
	}

	public SingletonMaxCSP3Single(Solver solver) {
		super(solver);
		untestedVariables = new boolean[solver.pb.variables.length];
		branch = new Branch(solver);
		combinator = new CombinatorOfTwoInts(solver.pb.stuff.maxVarDegree());
	}

	protected void undoAssignmentsFromBranch(Branch branch) {
		for (int i = branch.size - 1; i >= 0; i--)
			solver.backtrack(branch.vars[i]);
	}

	protected boolean manageInconsistentAssignment(Variable var, int idx) {
		nbEffectiveSingletonTests++;
		var.dom.removeElementary(idx);
		// System.out.println("sac removal of " + variable + " " + index);

		if (var.dom.size() == 0)
			return false;

		assert queue.isEmpty();
		// if (!super.checkArcConsistencyAfterRefutationOf(variable, solver.getCurrentDepth() + 1))
		// return false;
		// initialize();
		return true;
	}

	protected boolean canTryAnotherExtensionInsteadOf(Variable var, int idx) {
		if (!maximumBranchExtension || branch.size == 0)
			return false;

		// System.out.println("removal " + variable + " " + index);
		var.dom.removeElementary(idx);
		if (var.dom.size() == 0)
			return false;

		// assert (variable.getCurrentDomainSize() != 0);
		boolean b = super.runAfterRefutation(var);
		// System.out.println("Possibility of continuing = " + b + " size " + variable.getCurrentDomainSize());
		return b;
	}

	protected void dealWithNewBranch(Branch branch) {
		// branch.display();
		undoAssignmentsFromBranch(branch);
		cumulBranchSizes += branch.size;
		nbBuiltBranches++;
		// System.out.println("branch recorded nbUntested = " + nbUntestedVariables);
		// branch.display();
	}

	private Variable selectNextVariable(boolean onlyUntested) {
		bestScoredVariable.reset(false);
		solver.futVars.execute(x -> {
			if (!onlyUntested || untestedVariables[x.num]) {
				assert !onlyUntested || !branch.has(x);
				double result = selectionMode == 0 ? x.wdeg() / x.dom.size() : -combinator.combinedMaxMinLongValueFor(x.dom.size(), x.ddeg());
				// double result = future.getDynamicDegree() / (double) future.domain.getCurrentSize(); //TODO
				bestScoredVariable.update(x, result);
			}
		});
		assert bestScoredVariable.variable != null : "onlyUntested = " + onlyUntested;
		return bestScoredVariable.variable;
	}

	private int selectionMode = 0;

	protected boolean buildBranch(Branch branch) {
		branch.clear();
		// if (selectionMode == 0)
		// selectionMode = 1;
		// else
		// selectionMode = 0;
		boolean finished = false;
		while (!finished) {
			Variable var = (lastFailedVariable != null ? lastFailedVariable : selectNextVariable(nbUntestedVariables > 0));
			int idx = (lastFailedVariable != null ? lastFailedIndex : var.dom.first());
			lastFailedVariable = null;

			assert !var.isAssigned();
			assert var.dom.isPresent(idx);
			assert queue.isEmpty();

			nbSingletonTests++;
			// System.out.println("assgn " + variable + " " + index);
			solver.assign(var, idx);
			boolean consistent = super.runAfterAssignment(var);

			if (consistent) {
				setUntested(var.num, false);
				branch.add(var, idx);
				if (solver.depth() == solver.pb.variables.length) {
					// solver.dealWithNewSolution();
					finished = true;
				}
			} else {
				solver.backtrack(var);
				if (branch.size == 0)
					return manageInconsistentAssignment(var, idx);
				finished = !canTryAnotherExtensionInsteadOf(var, idx);
				if (finished) {
					lastFailedVariable = var;
					lastFailedIndex = idx;
				}
			}
		}

		dealWithNewBranch(branch);
		return true;
	}

	protected boolean filterBySAC() {
		if (solver.futVars.size() == 0)
			return true;

		nbBuiltBranches = 0;
		cumulBranchSizes = 0;

		initializeSingleton();
		while (nbUntestedVariables > 0) {
			boolean consistent = buildBranch(branch);
			if (!consistent)
				return false;
			if (solver.finished())
				return true;
			// tester juste la derniere valeur echouee si nbUntestedVariable = 0

		}
		if (!super.runAfterRefutation(null))
			return false;

		// System.out.println("nb = " + nbBuiltBranches + " sum = " + cumulBranchSizes + " avg ="
		// + (nbBuiltBranches > 0 ? cumulBranchSizes / (double) nbBuiltBranches : 0));

		return true;
	}

	@Override
	public boolean runInitially() {
		increment = true;
		if (!super.runInitially())
			return false;
		return filterBySAC();
	}

	@Override
	public boolean runAfterAssignment(Variable var) {
		return super.runAfterAssignment(var);

		// if (!super.checkConsistencyAfterAssignmentOf(variable))
		// return false;
		// return filterBySAC();
	}

	@Override
	public boolean runAfterRefutation(Variable var) {
		return super.runAfterRefutation(var);

		// if (!super.checkConsistencyAfterRefutationOf(variable, variableDepth))
		// return false;
		// return filterBySAC();
	}

	private boolean controlUntested() {
		int cpt = 0;
		for (int i = 0; i < untestedVariables.length; i++) {
			if (untestedVariables[i]) {
				if (!solver.pb.variables[i].isFuture())
					return false;
				cpt++;
			}
		}
		return cpt == nbUntestedVariables;
	}

}
