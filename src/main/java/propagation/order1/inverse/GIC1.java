/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.order1.inverse;

import java.util.stream.Stream;

import constraints.Constraint;
import constraints.extension.CtrExtensionSTR1;
import constraints.extension.CtrExtensionSTR3;
import heuristics.variables.HeuristicVariables;
import heuristics.variables.dynamic.WDegOnDom;
import propagation.order1.StrongConsistency;
import search.Solver;
import search.backtrack.SolverBacktrack;
import utility.Enums.EStopping;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public class GIC1 extends StrongConsistency {

	protected HeuristicVariables variableHeuristicForInverse;

	public int[] nInverseTests;
	public int nITests;

	private long baseNbSolutionsLimit;

	public GIC1(Solver solver) {
		super(solver);
		Kit.control(cp().settingRestarts.cutoff == Long.MAX_VALUE, () -> "With Inverse, there is currently no possibility of restarts.");
		Kit.control(!Stream.of(solver.pb.constraints).anyMatch(c -> c.getClass().isAssignableFrom(CtrExtensionSTR3.class)),
				() -> "Inverse currently not compatible with STR3");
		variableHeuristicForInverse = new WDegOnDom((SolverBacktrack) solver, false);
		nInverseTests = new int[solver.pb.variables.length + 1];
		baseNbSolutionsLimit = solver.solManager.limit;
	}

	protected void handleNewSolution(Variable x, int a) {}

	protected boolean isInverse(Variable x, int a) {
		nInverseTests[solver.depth()]++;
		nITests++;
		solver.resetNoSolutions();
		solver.assign(x, a);
		HeuristicVariables h = ((SolverBacktrack) solver).heuristicVars;
		((SolverBacktrack) solver).heuristicVars = variableHeuristicForInverse;
		solver.solManager.limit = 1;
		boolean inverse = enforceArcConsistencyAfterAssignment(x) && solver.doRun().stoppingType == EStopping.REACHED_GOAL;
		solver.solManager.limit = baseNbSolutionsLimit;
		((SolverBacktrack) solver).heuristicVars = h;
		if (inverse)
			handleNewSolution(x, a);
		else
			Kit.log.info(x + "=" + a + " is not inverse");
		solver.backtrack(x);
		return inverse;
	}

	protected void updateSTRStructures() {
		for (Constraint c : solver.pb.constraints)
			if (c instanceof CtrExtensionSTR1) { // || constraint instanceof AllDifferent) {
				int bef = solver.pb.nValuesRemoved;
				((CtrExtensionSTR1) c).runPropagator(null); // to update tables
				Kit.control(solver.pb.nValuesRemoved == bef);
			}
	}

	protected long before() {
		performingProperSearch = true;
		return solver.solManager.found;
	}

	protected void after(long nSolutionsBefore, int nValuesRemoved) {
		if (verbose >= 1) // && nbValuesRemoved > 0)
			Kit.log.info("nbGICInconsistentValues=" + nValuesRemoved + " at depth=" + solver.depth() + " for " + nInverseTests[solver.depth()] + " tests");
		solver.resetNoSolutions();
		solver.solManager.found = nSolutionsBefore;
		updateSTRStructures();
		performingProperSearch = false;
	}

	@Override
	public boolean enforceStrongConsistency() {
		long nSolutionsBefore = before();
		int nValuesRemoved = 0;
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			Domain dom = x.dom;
			for (int a = dom.first(); a != -1; a = dom.next(a))
				if (!isInverse(x, a)) {
					x.dom.removeElementary(a);
					nValuesRemoved++;
				}
			Kit.control(dom.size() != 0, () -> "Not possible to reach inconsistency with GIC (or your instance is unsat)");
		}
		after(nSolutionsBefore, nValuesRemoved);
		return true;
	}
}
