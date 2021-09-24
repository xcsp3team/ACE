/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package learning;

import java.util.Arrays;

import constraints.Constraint;
import propagation.GAC;
import solver.FutureVariables;
import utility.Kit;
import variables.Variable;

public final class ReductionOperators {

	/**
	 * The recorder to which this object is attached
	 */
	private final IpsRecorder recorder;

	/**
	 * indicates if (G)AC is guaranteed
	 */
	private final boolean acGuaranteed;

	/**
	 * indicates if there is no constraint involving more than 2 variables
	 */
	private final boolean binaryNetwork;

	private boolean eliminateEntailedVariables;
	private boolean eliminateInitialDomainVariables;
	private boolean eliminateJustifiedVariables;
	private boolean eliminateDegreeVariables;
	private boolean eliminateNotInProofVariables;

	/**
	 * The variables of the problem (redundant field)
	 */
	private final Variable[] variables;

	private final boolean[] selectedVariables;

	private final int[] tmpVariable;

	private final Constraint[] nonUniversal;

	private double nSEliminables;
	private double nREliminables;
	private double nIEliminables;
	private double nDEliminables;
	private double nPEliminables;

	private int nExtractions;

	public double proportionOfSEliminableVariables() {
		return nSEliminables / nExtractions;
	}

	public double proportionOfREliminableVariables() {
		return nREliminables / nExtractions;
	}

	public double proportionOfIEliminableVariables() {
		return nIEliminables / nExtractions;
	}

	public double proportionOfDEliminableVariables() {
		return nDEliminables / nExtractions;
	}

	public double proportionOfPEliminableVariables() {
		return nPEliminables / nExtractions;
	}

	public final boolean enablePElimination() {
		return eliminateNotInProofVariables;
	}

	private boolean parse(char c) {
		return c == '0' ? false : c == '1' ? true : (Boolean) Kit.exit("The expected character should have been 0 or 1");
	}

	public ReductionOperators(IpsRecorder recorder) {
		this.recorder = recorder;
		this.acGuaranteed = recorder.solver.propagation.getClass() == GAC.class && ((GAC) recorder.solver.propagation).guaranteed;
		this.binaryNetwork = recorder.solver.problem.features.maxCtrArity() == 2;
		String s = recorder.solver.head.control.learning.stateOperators;
		Kit.control(s.length() == 5);
		this.eliminateEntailedVariables = parse(s.charAt(0));
		this.eliminateInitialDomainVariables = parse(s.charAt(1));
		this.eliminateDegreeVariables = parse(s.charAt(2));
		this.eliminateJustifiedVariables = parse(s.charAt(3));
		this.eliminateNotInProofVariables = parse(s.charAt(4));
		if (eliminateNotInProofVariables && recorder instanceof IpsRecorderEquivalence) {
			this.eliminateNotInProofVariables = false;
			Kit.log.warning("partial state operator 'eliminateNotInProofVariables' set to false");
		}
		this.variables = recorder.solver.problem.variables;
		this.selectedVariables = new boolean[variables.length];
		this.tmpVariable = new int[variables.length];

		this.nonUniversal = eliminateDegreeVariables ? new Constraint[variables.length] : null;
	}

	private boolean canEliminateSingleton(Variable x) {
		assert x.dom.size() == 1;
		if (!acGuaranteed) // TODO can we relax a little bit this condition?
			return false;
		if (binaryNetwork)
			return true;
		for (Constraint c : x.ctrs)
			if (c.nFreeVariables() > 1)
				return false;
		return true;
	}

	private void initEliminateDegree() {
		Arrays.fill(nonUniversal, null);
		for (Constraint c : recorder.solver.problem.constraints) {
			if (c.nFreeVariables() < 2)
				continue; // as the constraint is necessarily universal
			for (Variable x : c.scp) {
				if (nonUniversal[x.num] == null)
					nonUniversal[x.num] = c;
				else
					nonUniversal[x.num] = Constraint.TAG;
			}
		}
	}

	private boolean canEliminateDegree(Variable x) {
		Constraint c = nonUniversal[x.num];
		if (c == null)
			return true;
		if (c == Constraint.TAG)
			return false;
		int cnt = 0;
		for (Variable y : c.scp)
			if (nonUniversal[y.num] == Constraint.TAG)
				if (++cnt > 1)
					return false;
		return true;
	}

	private boolean canEliminate(Variable x) {
		if (eliminateEntailedVariables && x.dom.size() == 1 && canEliminateSingleton(x)) {
			nSEliminables++;
			return true;
		}
		if (eliminateInitialDomainVariables && x.dom.size() == x.dom.initSize()) {
			nREliminables++;
			return true;
		}
		if (eliminateDegreeVariables && canEliminateDegree(x)) {
			nDEliminables++;
			return true;
		}
		return false;
	}

	private boolean canEliminateDeduced(Variable x) {
		Constraint[] justification = recorder.explainer.justifications[x.num];
		for (int a = x.dom.lastRemoved(); a != -1; a = x.dom.prevRemoved(a)) {
			Constraint explanation = justification[a];
			if (explanation == null)
				return false;
			if (explanation == Constraint.TAG)
				continue;
			for (Variable y : explanation.scp)
				if (x != y && !selectedVariables[y.num])
					return false;
		}
		nIEliminables++;
		return true;
	}

	public int[] extract() {
		nExtractions++;
		int selectionLimit = 0;
		Arrays.fill(selectedVariables, false);
		if (eliminateDegreeVariables)
			initEliminateDegree();
		if (eliminateNotInProofVariables) {
			boolean[] proofVariables = recorder.solver.proofer.proofVariables[recorder.solver.depth()];
			// TODO paS PLUS 1 A PRIORI
			for (int i = 0; i < proofVariables.length; i++)
				if (proofVariables[i]) {
					if (!canEliminate(variables[i])) {
						tmpVariable[selectionLimit++] = i;
						selectedVariables[i] = true;
					}
				} else
					nPEliminables++;
		} else if (binaryNetwork) {
			FutureVariables futVars = recorder.solver.futVars;
			nSEliminables += futVars.nPast();
			for (Variable x = futVars.first(); x != null; x = futVars.next(x)) {
				if (!canEliminate(x)) {
					tmpVariable[selectionLimit++] = x.num;
					selectedVariables[x.num] = true;
				}
			}
		} else {
			for (Variable x : variables)
				if (!canEliminate(x)) {
					tmpVariable[selectionLimit++] = x.num;
					selectedVariables[x.num] = true;
				}
		}
		if (eliminateJustifiedVariables) {
			int cnt = 0;
			for (int i = 0; i < selectionLimit; i++)
				if (!canEliminateDeduced(variables[tmpVariable[i]]))
					tmpVariable[cnt++] = tmpVariable[i];
			selectionLimit = cnt;
		}
		int[] t = new int[selectionLimit];
		for (int i = 0; i < selectionLimit; i++)
			t[i] = tmpVariable[i];
		// System.out.println(solver.variables.length + " nbS=" + nSEliminables + " nbR=" + nREliminables + " nbI=" +
		// nIEliminables);
		return t;
	}

	public int[] extractForAllSolutions() {
		int selectionLimit = 0;
		if (binaryNetwork) {
			FutureVariables futVars = recorder.solver.futVars;
			nSEliminables += futVars.nPast();
			for (Variable x = futVars.first(); x != null; x = futVars.next(x)) {
				if (x.dom.size() == 1 && canEliminateSingleton(x))
					tmpVariable[selectionLimit++] = x.num;
			}
		} else {
			for (Variable x : variables)
				if (x.dom.size() == 1 && canEliminateSingleton(x))
					tmpVariable[selectionLimit++] = x.num;
		}
		int[] variableIndices = new int[selectionLimit];
		System.arraycopy(tmpVariable, 0, variableIndices, 0, selectionLimit);
		return variableIndices;
	}

	public int[] extract2() {
		nExtractions++;
		boolean[] proofVariables = recorder.solver.proofer.proofVariables[recorder.solver.depth()];
		int selectionLimit = 0;
		for (int i = 0; i < variables.length; i++) {
			if (proofVariables[i]) {
				// if (canEliminate(solver.getVariable(i)))
				// ; // System.out.println("ok " + solver.getVariable(i).domain.getCurrentSize());
				// else
				tmpVariable[selectionLimit++] = i;
			}
		}
		// System.out.println("selectionLimit = " + selectionLimit);
		int[] t = new int[selectionLimit];
		for (int i = 0; i < selectionLimit; i++)
			t[i] = tmpVariable[i];
		return t;
	}
}

//
// int[] t = new int[selectionLimit];
// for (int i = 0; i < selectionLimit; i++)
// t[i] = tmpVariable[i];
// // System.arraycopy(tmpVariable, 0, t, 0, selectionLimit);
//
// // System.out.println("size = " + selectionLimit);
// // System.out.println(solver.variables.length + " nbS=" + nbSEliminableVariables + " nbR=" + nbREliminableVariables +
// " nbI=" + nbIEliminableVariables); // + " " + cpt);
// return t;
// }

// if (reductionMode == 2 || reductionMode == 3) {
// int nbSelectedVariables = 0;
// for (int i = 0; i < selectionLimit; i++) {
// Variable variable = solver.getVariable(tmpVariable[i]);
// if (canEliminateDeduced(variable))
// tmpVariable[i] = -1;
// else
// nbSelectedVariables++;
// }
// t = new int[nbSelectedVariables];
// int cnt = 0;
// for (int i = 0; i < selectionLimit; i++)
// if (tmpVariable[i] != -1 && selectedVariables[solver.getVariable(tmpVariable[i]).getId()])
// t[cnt++] = tmpVariable[i];
// }
