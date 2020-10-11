/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.order1.weak;

import constraints.Constraint;
import constraints.hard.extension.CtrExtensionSTR1;
import constraints.hard.extension.structures.Table;
import interfaces.TagExperimental;
import search.Solver;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import utility.sets.SetDenseReversible;
import variables.Variable;

public class Weak3 extends Weak1 implements TagExperimental {

	protected boolean onlyOnePass = false;

	public Weak3(Solver solver) {
		super(solver);
	}

	protected boolean tryRefutationOf(Constraint c, int[] tuple) {
		int topStack = ((SolverBacktrack) solver).observerVars.top;
		for (int i = 0; i < c.scp.length; i++)
			c.scp[i].dom.reduceToElementary(tuple[i]);
		solver.restarter.currCutoff = cp().settingPropagation.weakCutoff;
		solver.doRun();
		boolean consistent = !(solver.isFullExploration() && solver.solManager.found == 0);
		if (solver.isFullExploration())
			solver.stoppingType = null;
		for (Variable x : c.scp)
			x.dom.restoreAtMark();
		((SolverBacktrack) solver).observerVars.top = topStack;
		// consistent = true;
		if (!consistent)
			nEffectiveSingletonTests++;
		return consistent;
	}

	// private int[] frontiers;

	private int filterConstraint(CtrExtensionSTR1 c) {
		Table table = (Table) c.extStructure();
		for (Variable x : c.scp)
			x.dom.setMark();
		int cnt = 0;
		((SolverBacktrack) solver).heuristicVars.setPriorityVars(c.scp, c.scp.length);
		SetDenseReversible denseSetOfTuples = c.set;
		int[] dense = denseSetOfTuples.dense;
		int i = 0;
		while (i <= denseSetOfTuples.limit) {
			int[] checkedTuple = table.tuples[dense[i]];
			Kit.log.finest(() -> " try tuple of " + c + " " + Kit.join(checkedTuple));
			boolean consistent = tryRefutationOf(c, checkedTuple);
			if (!consistent) {
				Kit.log.finest(() -> "removal of tuple " + Kit.join(checkedTuple));
				// constraint.remove(i, 0);
				cnt++;
			} else
				i++;
		}
		((SolverBacktrack) solver).heuristicVars.resetPriorityVars();
		return cnt;
	}

	@Override
	protected boolean enforceStrongConsistency() {
		boolean modified = true;
		while (modified) {
			modified = false;
			Constraint[] ctrs = solver.pb.constraints;
			for (int i = ctrs.length - 1; i >= 0; i--) {
				Constraint c = ctrs[i];
				if (!(c instanceof CtrExtensionSTR1))
					continue;
				int nbRemovals = filterConstraint((CtrExtensionSTR1) c);
				Kit.log.finest(() -> "   check of " + c + " give " + nbRemovals + " removals of tuples");
				if (nbRemovals > 0) {
					modified = true;
					// if (!checkConsistencyAfterRefutationOf(variable,
					// solver.getCurrentDepth() + 1))
					// return false;
				}
				if (solver.finished())
					return true;
			}
			if (onlyOnePass) {
				modified = false;
				((SolverBacktrack) solver).heuristicVars.reset(); // ((SolverBacktrack) solver).heuristicVars.solver.
				// for (Constraint d : solver.pb.constraints)
				// d.resetWdeg();
			}
			Kit.log.finest(() -> "   after pass, nbTuplesRemoved = " + pb().nTuplesRemoved + " \n");
		}
		int before = pb().nValuesRemoved;
		if (!enforceArcConsistency())
			return false;
		nPreproRemovals = pb().nValuesRemoved - before;
		Kit.log.finest(() -> "\n   nbACRemovals = " + nPreproRemovals);

		cp().settingRestarts.nRunsLimit = 0;
		return true;
	}
}
