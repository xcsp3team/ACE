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

public final class IpsExtractor {

	/**
	 * The IPS reasoner to which this object is attached
	 */
	private final IpsReasoner ipsReasoner;

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

	private final Variable[] tmpVariable;

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

	public IpsExtractor(IpsReasoner ipsReasoner) {
		this.ipsReasoner = ipsReasoner;
		this.acGuaranteed = ipsReasoner.solver.propagation.getClass() == GAC.class && ((GAC) ipsReasoner.solver.propagation).guaranteed;
		this.binaryNetwork = ipsReasoner.solver.problem.features.maxCtrArity() == 2;
		String s = ipsReasoner.solver.head.control.learning.ipsOperators;
		Kit.control(s.length() == 5);
		this.eliminateEntailedVariables = parse(s.charAt(0));
		this.eliminateInitialDomainVariables = parse(s.charAt(1));
		this.eliminateDegreeVariables = parse(s.charAt(2));
		this.eliminateJustifiedVariables = parse(s.charAt(3));
		this.eliminateNotInProofVariables = parse(s.charAt(4));
		if (eliminateNotInProofVariables && ipsReasoner instanceof IpsReasonerEquivalence) {
			this.eliminateNotInProofVariables = false;
			Kit.log.warning("partial state operator 'eliminateNotInProofVariables' set to false");
		}
		this.variables = ipsReasoner.solver.problem.variables;
		this.selectedVariables = new boolean[variables.length];
		this.tmpVariable = new Variable[variables.length];

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
		for (Constraint c : ipsReasoner.solver.problem.constraints) {
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
		Constraint[] justification = ipsReasoner.explainer.justifications[x.num];
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

	public Variable[] extract() {
		nExtractions++;
		int cnt = 0;
		Arrays.fill(selectedVariables, false);
		if (eliminateDegreeVariables)
			initEliminateDegree();
		if (eliminateNotInProofVariables) {
			boolean[] proofVariables = ipsReasoner.solver.proofer.proofVariables[ipsReasoner.solver.depth()];
			// TODO paS PLUS 1 A PRIORI
			for (int i = 0; i < proofVariables.length; i++)
				if (proofVariables[i]) {
					if (!canEliminate(variables[i])) {
						tmpVariable[cnt++] = variables[i];
						selectedVariables[i] = true;
					}
				} else
					nPEliminables++;
		} else if (binaryNetwork) {
			FutureVariables futVars = ipsReasoner.solver.futVars;
			nSEliminables += futVars.nPast();
			for (Variable x = futVars.first(); x != null; x = futVars.next(x)) {
				if (!canEliminate(x)) {
					tmpVariable[cnt++] = x;
					selectedVariables[x.num] = true;
				}
			}
		} else {
			for (Variable x : variables)
				if (!canEliminate(x)) {
					tmpVariable[cnt++] = x;
					selectedVariables[x.num] = true;
				}
		}
		if (eliminateJustifiedVariables) {
			int cntbis = 0;
			for (int i = 0; i < cnt; i++)
				if (!canEliminateDeduced(tmpVariable[i]))
					tmpVariable[cntbis++] = tmpVariable[i];
			cnt = cntbis;
		}
		Variable[] t = new Variable[cnt];
		for (int i = 0; i < cnt; i++)
			t[i] = tmpVariable[i];
		// System.out.println(variables.length + " nbS=" + nSEliminables + " nbR=" + nREliminables + " nbI=" +
		// nIEliminables);
		return t;
	}

	public Variable[] extractForAllSolutions() {
		int cnt = 0;
		if (binaryNetwork) {
			FutureVariables futVars = ipsReasoner.solver.futVars;
			nSEliminables += futVars.nPast();
			for (Variable x = futVars.first(); x != null; x = futVars.next(x)) {
				if (x.dom.size() == 1 && canEliminateSingleton(x))
					tmpVariable[cnt++] = x;
			}
		} else {
			for (Variable x : variables)
				if (x.dom.size() == 1 && canEliminateSingleton(x))
					tmpVariable[cnt++] = x;
		}
		Variable[] t = new Variable[cnt];
		for (int i = 0; i < cnt; i++)
			t[i] = tmpVariable[i];
		return t;
	}

	public Variable[] extract2() {
		nExtractions++;
		boolean[] proofVariables = ipsReasoner.solver.proofer.proofVariables[ipsReasoner.solver.depth()];
		int cnt = 0;
		for (int i = 0; i < variables.length; i++) {
			if (proofVariables[i]) {
				// if (canEliminate(variables[i])) System.out.println("ok " + variables[i].dom.getCurrentSize());
				// else
				tmpVariable[cnt++] = variables[i];
			}
		}
		Variable[] t = new Variable[cnt];
		for (int i = 0; i < cnt; i++)
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
