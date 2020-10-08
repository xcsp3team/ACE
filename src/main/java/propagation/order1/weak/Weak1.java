/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.order1.weak;

import interfaces.TagExperimental;
import propagation.order1.StrongConsistency;
import search.Solver;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public class Weak1 extends StrongConsistency implements TagExperimental {

	// protected boolean initializeWeights = false; // TODO hard coding
	//
	// protected int[] cumulWeights;

	protected Variable[] selectedVariables;

	private Variable[] priorityVariable = new Variable[1];

	public Weak1(Solver solver) {
		super(solver);
		Kit.control(solver.pb.priorityVars.length == 0);
		/*
		 * int nb = Arguments.getNbReadArguments(); String[] args = Arguments.getCommandLineArguments(); if (args.length != nb) { selectedVariables =
		 * new Variable[args.length - nb]; for (int i = nb; i < args.length; i++) selectedVariables[i - nb] =
		 * solver.problem.getVariable(Integer.parseInt(args[i])); }
		 */
		// if (initializeWeights)
		// cumulWeights = new int[solver.pb.variables.length];
	}

	protected boolean tryToRefute(Variable x, int a) {
		performingProperSearch = true;
		nSingletonTests++;
		solver.resetNoSolutions();
		solver.setDomainsMarks();
		solver.assign(x, a);
		solver.restarter.currCutoff = solver.restarter.measureSupplier.get() + cp().settingPropagation.weakCutoff;
		boolean inconsistent = !enforceArcConsistencyAfterAssignment(x) || (solver.doRun().solManager.nSolutionsFound == 0 && solver.isFullExploration());
		// if (!inverse) System.out.println(variable + "=" + index + " is not inverse");
		solver.backtrack(x);
		solver.restoreDomainsAtMarks();
		if (inconsistent)
			nEffectiveSingletonTests++;
		solver.resetNoSolutions();
		performingProperSearch = false;
		return !inconsistent;
	}

	protected int performInferencesFrom(Variable x) {
		Domain dom = x.dom;
		int sizeBefore = dom.size();
		if (onlyBounds) {
			while (dom.size() > 0 && !tryToRefute(x, dom.first()))
				x.dom.removeElementary(dom.first());
			while (dom.size() > 1 && !tryToRefute(x, dom.last()))
				x.dom.removeElementary(dom.last());
		} else {
			for (int a = dom.first(); a != -1;) {
				int b = dom.next(a);
				if (cp().verbose > 2)
					Kit.log.finest("try " + x + " " + a);
				// if (initializeWeights)
				// pb().resetWdeg();
				if (!tryToRefute(x, a)) {
					x.dom.removeElementary(a);
				} else {
					// if (initializeWeights)
					// for (Variable y : solver.pb.variables)
					// cumulWeights[y.num] += y.wdeg - y.ctrs.length;
				}
				a = b;
			}
		}
		return sizeBefore - dom.size();
	}

	@Override
	protected boolean enforceStrongConsistency() {
		for (int cnt = 0; cnt < nPassesLimit; cnt++) {
			int nbTotalRemovals = 0;
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				priorityVariable[0] = x;
				((SolverBacktrack) solver).heuristicVars.setPriorityVars(priorityVariable, 1);
				int nbRemovals = performInferencesFrom(x);
				((SolverBacktrack) solver).heuristicVars.resetPriorityVars();
				if (cp().verbose > 2)
					Kit.log.info("   check of " + x + " give " + nbRemovals + " removals");
				if (nbRemovals > 0) {
					nbTotalRemovals += nbRemovals;
					if (x.dom.size() == 0)
						return false;
					if (!enforceArcConsistencyAfterRefutation(x))
						return false;
				}
				if (solver.finished())
					return true;
			}
			if (cp().verbose > 1)
				Kit.log.info("Weak1 Pass " + cnt + " nbTotalRemovals=" + nbTotalRemovals + " nbValuesRemoved=" + Variable.nRemovedValuesFor(solver.pb.variables)
						+ (nbTotalRemovals == 0 ? "\n" : ""));
			if (nbTotalRemovals == 0)
				break;
		}
		cp().settingRestarts.nRunsLimit = 1;
		// if (initializeWeights)
		// for (Variable x : solver.pb.variables)
		// x.wdeg = cumulWeights[x.num] + x.ctrs.length;
		return true;
	}

	@Override
	protected boolean enforceMore() {
		long c = solver.restarter.currCutoff;
		boolean consistent = super.enforceMore();
		solver.restarter.currCutoff = c;
		return consistent;
	}

}

/*
 * // il est necessaire que la premi�re variable assign�e soit futureVariable ; autrement on risque d'apprendre de mauvaises inf�rences d'un run �
 * l'autre si onr encontre des valeurs non sac protected boolean tryRefutationOf(Variable variable, int index) { if (Data.boundConsistency &&
 * !variable.checkBackwardConsistencyOf(index)) return false;
 * 
 * nbSingletonTests++;
 * 
 * int topStack = solver.getVariablesObserver().getTop(); variable.domain.getElements().setMark(); ((ForwardPropagation)
 * solver.propagation).setFilteringOptimization(false);
 * 
 * variable.domain.reduceToValueAt(index); solver.getRestarter().setCurrentCutoff(Data.weakCutoff); // Kit.prn(futureVariable + " " + index);
 * solver.doRun(); boolean consistent = !(solver.isFullExploration() && solver.solutionManager.getNbSolutionsFound() == 0); if (!consistent)
 * nbEffectiveSingletonTests++; if (solver.isFullExploration()) solver.setStoppingType(null);
 * 
 * ((ForwardPropagation) solver.propagation).setFilteringOptimization(true); variable.domain.getElements().restoreAtMark();
 * solver.getVariablesObserver().setTop(topStack);
 * 
 * return consistent; }
 */
