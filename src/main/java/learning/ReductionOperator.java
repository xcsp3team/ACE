/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package learning;

import java.util.Arrays;

import constraints.Constraint;
import propagation.order1.AC;
import search.Solver;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public final class ReductionOperator {
	private LearnerStates learner;

	private boolean isGACGuaranteed;

	private boolean binaryNetwork;

	private final boolean[] selectedVariables;

	private boolean eliminateEntailedVariables;
	private boolean eliminateInitialDomainVariables;
	private boolean eliminateJustifiedVariables;
	private boolean eliminateDegreeVariables;
	private boolean eliminateNotInProofVariables;

	private double nbSEliminableVariables;
	private double nbREliminableVariables;
	private double nbIEliminableVariables;
	private double nbDEliminableVariables;
	private double nbPEliminableVariables;

	private int nbExtractions;

	private final int[] tmpVariable;

	public double getProportionOfNbSEliminableVariables() {
		return nbSEliminableVariables / nbExtractions;
	}

	public double getProportionOfNbREliminableVariables() {
		return nbREliminableVariables / nbExtractions;
	}

	public double getProportionOfNbIEliminableVariables() {
		return nbIEliminableVariables / nbExtractions;
	}

	public double getProportionOfNbDEliminableVariables() {
		return nbDEliminableVariables / nbExtractions;
	}

	public double getProportionOfNbPEliminableVariables() {
		return nbPEliminableVariables / nbExtractions;
	}

	public boolean enablePElimination() {
		return eliminateNotInProofVariables;
	}

	private boolean parse(char c) {
		return c == '0' ? false : c == '1' ? true : (Boolean) Kit.exit("The expected character should have been 0 or 1");
	}

	private void parseReductionMode(String s) {
		Kit.control(s.length() == 5);
		eliminateEntailedVariables = parse(s.charAt(0));
		eliminateInitialDomainVariables = parse(s.charAt(1));
		eliminateDegreeVariables = parse(s.charAt(2));
		eliminateJustifiedVariables = parse(s.charAt(3));
		eliminateNotInProofVariables = parse(s.charAt(4));
		if (eliminateNotInProofVariables && learner instanceof LearnerStatesEquivalence) {
			eliminateNotInProofVariables = false;
			Kit.log.warning("partial state operator 'eliminateNotInProofVariables' set to false");

		}

	}

	public ReductionOperator(LearnerStates learner) {
		this.learner = learner;
		Solver solver = learner.solver;
		isGACGuaranteed = solver.propagation.getClass() == AC.class && Constraint.isGuaranteedGACOn(solver.pb.constraints);
		binaryNetwork = solver.pb.stuff.maxCtrArity() == 2;
		tmpVariable = new int[solver.pb.variables.length];
		parseReductionMode(learner.solver.rs.cp.learning.stateOperators);
		// Kit.control(!eliminateNotInProofVariables || !(stateRecordingManager instanceof StateEquivalenceManager));
		selectedVariables = new boolean[solver.pb.variables.length];
	}

	private int getNbFreeVariablesIn(Constraint ctr) {
		int cnt = 0;
		for (int i = ctr.futvars.limit; i >= 0; i--)
			if (ctr.scp[ctr.futvars.dense[i]].dom.size() != 1)
				cnt++;
		return cnt;
	}

	private boolean canEliminateSingleton(Variable x) {
		assert x.dom.size() == 1;
		if (!isGACGuaranteed)
			return false;
		if (binaryNetwork)
			return true;
		for (Constraint c : x.ctrs)
			if (getNbFreeVariablesIn(c) > 1)
				return false;
		return true;
	}

	private Constraint[] nonUniversal;

	private void initEliminateDegree() {
		if (nonUniversal == null)
			nonUniversal = new Constraint[learner.solver.pb.variables.length];
		else
			Arrays.fill(nonUniversal, null);
		for (Constraint c : learner.solver.pb.constraints) {
			if (getNbFreeVariablesIn(c) < 2)
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

	public boolean canEliminate(Variable x) {
		if (eliminateEntailedVariables && x.dom.size() == 1 && canEliminateSingleton(x)) {
			nbSEliminableVariables++;
			return true;
		}
		if (eliminateInitialDomainVariables && x.dom.size() == x.dom.initSize()) {
			nbREliminableVariables++;
			return true;
		}
		if (eliminateDegreeVariables && canEliminateDegree(x)) {
			nbDEliminableVariables++;
			return true;
		}
		return false;
	}

	private boolean canEliminateDeduced(Variable x) {
		Domain dom = x.dom;
		for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a)) {
			Constraint explanation = learner.justifier.justifications[x.num][a];
			if (explanation == null)
				return false;
			if (explanation == Constraint.TAG)
				continue;
			for (Variable y : explanation.scp)
				if (x != y && !selectedVariables[y.num])
					return false;
		}
		nbIEliminableVariables++;
		return true;
	}

	public int[] extract() {
		nbExtractions++;
		int selectionLimit = 0;
		Arrays.fill(selectedVariables, false);
		if (eliminateDegreeVariables)
			initEliminateDegree();
		Solver solver = learner.solver;
		Variable[] variables = solver.pb.variables;
		if (eliminateNotInProofVariables) {
			// System.out.println(" proof at level = " + (solver.getCurrentDepth() + 1));
			boolean[] proofVariables = ((SolverBacktrack) solver).proofer.getProofVariablesAt(solver.depth());
			// TODO paS PLUS 1 A PRIORI
			for (int i = 0; i < proofVariables.length; i++)
				if (proofVariables[i]) {
					if (!canEliminate(variables[i])) {
						tmpVariable[selectionLimit++] = i;
						selectedVariables[i] = true;
					}
				} else
					nbPEliminableVariables++;
		} else if (solver.pb.stuff.maxCtrArity() == 2) {
			nbSEliminableVariables += solver.futVars.nDiscarded();
			for (Variable x : solver.futVars) {
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
			int nbSelectedVariables = 0;
			for (int i = 0; i < selectionLimit; i++)
				if (!canEliminateDeduced(variables[tmpVariable[i]]))
					tmpVariable[nbSelectedVariables++] = tmpVariable[i];
			selectionLimit = nbSelectedVariables;
		}

		int[] t = new int[selectionLimit];
		for (int i = 0; i < selectionLimit; i++)
			t[i] = tmpVariable[i];
		// System.arraycopy(tmpVariable, 0, t, 0, selectionLimit);

		// System.out.println(solver.variables.length + " nbS=" + nbSEliminableVariables + " nbR=" +
		// nbREliminableVariables + " nbI=" + nbIEliminableVariables); // + " " + cpt);
		return t;
	}

	public int[] extractForAllSolutions() {
		Solver solver = learner.solver;
		int selectionLimit = 0;
		if (solver.pb.stuff.maxCtrArity() == 2) {
			nbSEliminableVariables += solver.futVars.nDiscarded();
			for (Variable x : solver.futVars) {
				if (x.dom.size() == 1 && canEliminateSingleton(x))
					tmpVariable[selectionLimit++] = x.num;
			}
		} else {
			for (Variable x : solver.pb.variables)
				if (x.dom.size() == 1 && canEliminateSingleton(x))
					tmpVariable[selectionLimit++] = x.num;
		}
		int[] variableIndices = new int[selectionLimit];
		System.arraycopy(tmpVariable, 0, variableIndices, 0, selectionLimit);
		return variableIndices;
	}

	// public int[] copy() {
	// return
	// Toolkit.buildArrayWithIntegerValues(stateRecordingManager.getSystematicSolver().getProblem().variables.length,
	// 0);
	// }

	public int[] extract2() {
		nbExtractions++;
		Solver solver = learner.solver;
		boolean[] proofVariables = ((SolverBacktrack) solver).proofer.getProofVariablesAt(solver.depth());
		int selectionLimit = 0;
		for (int i = 0; i < solver.pb.variables.length; i++) {
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
		// System.arraycopy(tmpVariable, 0, t, 0, selectionLimit);
		//
		// // System.out.println("size = " + selectionLimit);
		// // System.out.println(solver.variables.length + " nbS=" + nbSEliminableVariables + " nbR=" +
		// nbREliminableVariables + " nbI=" + nbIEliminableVariables); // + " " + cpt);
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
