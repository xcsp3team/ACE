/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.inverse;

import java.util.stream.Stream;

import constraints.Constraint;
import constraints.extension.ExtensionSTR1;
import constraints.extension.ExtensionSTR3;
import heuristics.HeuristicVariables;
import heuristics.HeuristicVariablesDynamic.WdegOnDom;
import propagation.StrongConsistency;
import search.Solver;
import search.backtrack.SolverBacktrack;
import utility.Enums.EStopping;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public class GIC1 extends StrongConsistency {

	protected HeuristicVariables heuristic;

	public int[] nInverseTests;
	public int nITests;

	private long baseNbSolutionsLimit;

	public GIC1(Solver solver) {
		super(solver);
		this.heuristic = new WdegOnDom((SolverBacktrack) solver, false);
		this.nInverseTests = new int[solver.pb.variables.length + 1];
		this.baseNbSolutionsLimit = solver.solManager.limit;
		Kit.control(solver.rs.cp.settingRestarts.cutoff == Long.MAX_VALUE, () -> "With GIC, there is currently no possibility of restarts.");
		Kit.control(!Stream.of(solver.pb.constraints).anyMatch(c -> c.getClass().isAssignableFrom(ExtensionSTR3.class)),
				() -> "GIC currently not compatible with STR3");

	}

	protected void handleNewSolution(Variable x, int a) {
	}

	protected boolean isInverse(Variable x, int a) {
		nInverseTests[solver.depth()]++;
		nITests++;
		solver.resetNoSolutions();
		solver.assign(x, a);
		HeuristicVariables h = ((SolverBacktrack) solver).heuristicVars;
		((SolverBacktrack) solver).heuristicVars = heuristic;
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
			if (c instanceof ExtensionSTR1) { // || constraint instanceof AllDifferent) {
				int bef = solver.pb.nValuesRemoved;
				((ExtensionSTR1) c).runPropagator(null); // to update tables
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
