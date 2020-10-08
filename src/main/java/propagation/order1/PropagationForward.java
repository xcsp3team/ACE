/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1;

import propagation.Propagation;
import propagation.order1.isomorphism.PropagationIsomorphism;
import propagation.structures.revisers.Reviser;
import search.Solver;
import search.backtrack.SolverBacktrack;
import utility.Enums.EBranching;
import utility.Reflector;
import variables.Variable;

public abstract class PropagationForward extends Propagation {

	/**
	 * The reviser object attached to the forward propagation object.
	 */
	public Reviser reviser;

	public PropagationForward(Solver solver) {
		super(solver);
		this.reviser = Reflector.buildObject(cp().settingPropagation.classForRevisions, Reviser.class, this);
	}

	protected final boolean hasSolverPropagatedAfterLastButOneDecision() {
		return cp().settingSolving.branching != EBranching.NON || !((SolverBacktrack) solver).dr.isLastButOneDecisionNegative();
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		assert x.isAssigned() && (queue.size() == 0 || this instanceof PropagationIsomorphism) : queue.size() + " " + x.isAssigned();
		queue.add(x);
		return propagate();
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		assert !x.isAssigned() && queue.size() == 0 && x.dom.size() > 0;
		queue.add(x);
		return propagate();
	}
}

// /**
// * Increments some counters related to the given constraint and the the given
// variable according to the values of
// <code> variableFailuresMode </code> and <code> valueFailuresMode </code>.
// *
// * @param constraint a constraint of the problem
// * @param variable a variable involved in the given constraint
// */
// public void incrementNbFailuresOf(Constraint constraint, Variable variable,
// int nbRemovals) {
// if (solver.getCurrentDepth() == 0)
// return;
// // if (!DomPlus.active)
// {
// int increment = Data.weightingIncrementMode == 0 ? 1 :
// solver.variables.length - solver.getCurrentDepth();
// constraint.incrementWeigthedDegreeOf(increment);
// Variable[] scope = constraint.getScope();
// for (int i = 0; i < scope.length; i++)
// scope[i].incrementWeightedDegreeOf(increment);
// }
//
// // if (DomPlus.residues != null) {
// // Variable lastPast = solver.getVariableManager().getLastPastVariable();
// // if (lastPast != null)
// // DomPlus.residues[lastPast.getId()][lastPast.domain.getUniqueIndex()]
// = variable;
// // }
// // if (DomPlus2.residues != null) {
// // Variable lastPast = solver.getVariableManager().getLastPastVariable();
// // if (lastPast != null)
// // DomPlus2.residues[lastPast.getId()][lastPast.domain.getUniqueIndex()]
// = constraint;
// // }
// }

// protected boolean controlConsistencyWithTightness = false; // false; TODO
// hard coding
//
// private boolean mustAvoidRevisionOf(Constraint constraint, Variable variable)
// {
// if (!controlConsistencyWithTightness) return false;
// int domainSizeBefore = variable.getCurrentDomainSize();
// int brotherSizeBefore =
// constraint.getFirstVariableDifferentFrom(variable).getCurrentDomainSize();
// double d = constraint.tightness;
// for (int i = 1; i < brotherSizeBefore; i++) d *= constraint.tightness;
// // if (domainSizeBefore > 5 && brotherSizeBefore > 5 &&
// Math.pow(constraint.tightness, brotherSizeBefore)
// domainSizeBefore < 0.0001)
// return (domainSizeBefore > 1 && brotherSizeBefore > 1 && (2 *
// solver.constraints.length * d * domainSizeBefore) < 1);
// }

// variable.incrementNbWipeouts();

// Variable last = solver.getVariableManager().getLastPastVariable();
// last.domain.incrementWeightOf(last.domain.getUniqueIndex());

// if (valueFailuresMode == 0)
// {
// int nbPastVariables = solver.getVariableManager().getNbPastVariables();
// for (Variable currentVariable : solver.variables)
// {
// if (!currentVariable.isAssigned())
// continue;
// currentVariable.domain.incrementWeightOf(currentVariable.domain.getFirstValidIndex(),
// nbPastVariables);
// }
// }
// else if (valueFailuresMode == 1)
// {
// Domain currentDomain =
// solver.getVariableManager().getLastPastVariable().domain;
// currentDomain.incrementWeightOf(currentDomain.getFirstValidIndex(),
// solver.variables.length -
// solver.getVariableManager().getNbPastVariables() + 1);
// }
// else if (valueFailuresMode == 2)
// {
// Variable[] variables = solver.variables;
// for (int i = 0; i < variables.length; i++)
// {
// if (!variables[i].isAssigned())
// continue;
// variables[i].domain.incrementWeightOf(variables[i].domain.getFirstValidIndex());
// }
// }
// else if (valueFailuresMode == 3)
// {
// double increment = 1.0 / solver.getCurrentDepth();
// Variable[] variables = solver.variables;
// for (int i = 0; i < variables.length; i++)
// {
// if (!variables[i].isAssigned())
// continue;
// variables[i].domain.incrementWeightOf(variables[i].domain.getFirstValidIndex(),
// increment);
// }
// }
// else if (valueFailuresMode == 4)
// {
// Variable[] variables = solver.variables;
// for (int i = 0; i < variables.length; i++)
// {
// if (!variables[i].isAssigned())
// continue;
// if (variable.isNeighbourOf(variables[i]))
// variables[i].domain.incrementWeightOf(variables[i].domain.getFirstValidIndex());
// }
// }
// else if (valueFailuresMode == 5)
// {
// Elements elements = variable.domain.getElements();
// for (int i = elements.getLastAbsent(); i != -1; i =
// elements.getPrevAbsent(i))
// {
// int removalLevel = elements.getAbsentLevelOf(i);
// if (removalLevel == 0)
// continue;
// // Kit.prn("remleveml" + removalLevel);
// Variable culprit = ((SystematicSolver)
// solver).getVariableManager().getAssignedVariableAt(removalLevel - 1);
// culprit.domain.incrementWeightOf(culprit.domain.getFirstValidIndex());
// }
// }

// protected SubstitutabilityManager substitutabilityManager; // = new
// SubstitutabilityManager1(this);
//
// public final boolean checkConsistencyOfPropagationSet() {
// if (substitutabilityManager == null)
// return super.checkConsistencyOfPropagationSet();
// boolean consistent = super.checkConsistencyOfPropagationSet();
// if (!consistent)
// return false;
// substitutabilityManager.removeSubstitutableValues();
// return true;
// }
