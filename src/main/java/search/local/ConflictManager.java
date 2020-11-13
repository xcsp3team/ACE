/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search.local;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.IntStream;

import org.xcsp.common.Types.TypeFramework;

import constraints.Constraint;
import dashboard.ControlPanel;
import sets.SetSparse;
import utility.Kit;
import variables.Variable;

public class ConflictManager {

	private final SolverLocal solver;

	private final SetSparse set; // conflicting constraints

	private int currEvaluation;

	private final int[] currVariableEvaluations;

	private long currCost = 0;

	public int nConflictingConstraints() {
		return set.limit + 1;
	}

	public int currEvaluation() {
		return currEvaluation;
	}

	public int currEvaluationOf(Variable x) {
		return currVariableEvaluations[x.num];
	}

	public int currEvaluationOf(Variable x, Variable y) {
		int evaluation = currVariableEvaluations[x.num] + currVariableEvaluations[y.num];
		// now supress double countings
		for (Constraint c : x.ctrs)
			if (c.involves(y) && !c.checkCurrentInstantiation())
				evaluation -= c.wdeg();
		return evaluation;
	}

	public void clear() {
		set.clear();
		Arrays.fill(currVariableEvaluations, 0);
	}

	public ConflictManager(SolverLocal localSolver) {
		this.solver = localSolver;
		this.set = new SetSparse(localSolver.pb.constraints.length);
		currVariableEvaluations = new int[localSolver.pb.variables.length];
	}

	public void recomputeEvaluations() {
		currEvaluation = 0;
		Arrays.fill(currVariableEvaluations, 0);
		Constraint[] ctrs = solver.pb.constraints;

		ControlPanel cp = solver.rs.cp;
		for (int i = set.limit; i >= 0; i--) {
			Constraint c = ctrs[set.dense[i]];
			// if (cp.hardCoding.weightingIncrementInConflictManager) // TODO because of refactoring, this must be updated
			// c.incrementWdegBy(1);
			currEvaluation += c.wdeg();
			for (Variable x : c.scp) {
				// if (x.decision)
				currVariableEvaluations[x.num] += c.wdeg();
				// else {
				// int[] predecessors = solverLocal.getPredecessors(x.num);
				// for (int j = 0; j < predecessors.length; j++)
				// currVariableEvaluations[solverLocal.decisionVars[predecessors[j]].num] += c.wdeg();
				// }
			}
		}
	}

	public void initializeConflictingConstraints() {
		clear();
		// for (Constraint ctr : problem.constraints)
		// if (((CtrHard) ctr).getDependantVariablePosition() == -1 && !((CtrHard) ctr).checkCurrentInstantiation())
		// addConflictingConstraint(ctr);
		recomputeEvaluations();
		if (solver.pb.settings.framework == TypeFramework.COP)
			currCost = solver.pb.optimizer.value();
	}

	//
	// public void addConflictingConstraint(Constraint ctr) {
	// sparseSetOfConflictingConstraints.add(ctr.num);
	// }
	//
	// public void removeConflictingConstraint(Constraint ctr) {
	// sparseSetOfConflictingConstraints.remove(ctr.num);
	// }
	//
	// public void updateConflictingConstraintsFromNewAssignmentOf(Variable var) {
	// // System.out.println();
	// // for (Variable v : localSolver.getProblem().variables)
	// // System.out.print(v.domain.getUniqueValue() + " ");
	//
	// for (Constraint ctr : var.ctrs)
	// // System.out.println("nb=" + getNbConflictingConstraints());
	// if (((CtrHard) ctr).getDependantVariablePosition() == -1)
	// if (!((CtrHard) ctr).checkCurrentInstantiation())
	// addConflictingConstraint(ctr);
	// else
	// removeConflictingConstraint(ctr);
	// }

	public boolean checkConflictingConstraints() {
		for (Constraint c : solver.pb.constraints)
			if (!c.checkCurrentInstantiation() && !set.isPresent(c.num)) {
				Kit.log.severe(c + " not satisfied and absent in sparse set.");
				return false;
			} else if (c.checkCurrentInstantiation() && set.isPresent(c.num)) {
				Kit.log.severe(c + " satisfied but present in sparse set.");
				return false;
			}
		return true;
	}

	public int computeEvolutionFor(Variable x, int a, int acceptableEvaluationLimit, Long currCostEvolution) {
		int evaluation = -currEvaluationOf(x);
		// int currentIndex = var.dom.forcedIndex;
		// var.dom.forcedIndex = idx;
		solver.propagateDependentVariables();
		Set<Constraint> constraintsToCheck = new HashSet<>();
		for (int i : solver.getSuccessors(x.num))
			for (Constraint c : solver.pb.variables[i].ctrs)
				constraintsToCheck.add(c);
		for (Constraint c : constraintsToCheck) {
			if (!c.checkCurrentInstantiation())
				evaluation += c.wdeg();
			if (evaluation > acceptableEvaluationLimit)
				break;
		}
		if (solver.pb.settings.framework == TypeFramework.COP) {
			assert currCostEvolution != null;
			currCostEvolution = solver.pb.optimizer.value() - currCost;
		}
		// var.dom.forcedIndex = currentIndex;
		return evaluation;
	}

	public int computeEvolutionFor(Variable x, int a, int acceptableEvaluationLimit) {
		return computeEvolutionFor(x, a, acceptableEvaluationLimit, null);
	}

	public int computeEvolutionFor(Variable x, int a, Variable y, int b, int acceptableEvaluationLimit) {
		int evaluation = -currEvaluationOf(x, y);
		solver.propagateDependentVariables();
		for (Constraint c : x.ctrs) {
			if (!c.checkCurrentInstantiation())
				evaluation += c.wdeg();
			if (evaluation > acceptableEvaluationLimit)
				break;
		}
		for (Constraint c : y.ctrs) {
			if (c.involves(x))
				continue;
			if (!c.checkCurrentInstantiation())
				evaluation += c.wdeg();
			if (evaluation > acceptableEvaluationLimit)
				break;
		}
		return evaluation;
	}

	public int computeEvolutionFor(Variable x, int a) {
		return computeEvolutionFor(x, a, Integer.MAX_VALUE);
	}

	public void displayConflictingConstraints() {
		IntStream.rangeClosed(0, set.limit).mapToObj(i -> solver.pb.constraints[set.dense[i]]).forEach(c -> c.display(false));
	}

}