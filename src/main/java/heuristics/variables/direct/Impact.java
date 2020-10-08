/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics.variables.direct;

import java.util.Arrays;

import search.backtrack.SolverBacktrack;
import utility.Kit;
import variables.Variable;

public final class Impact extends ActivityImpactAbstract {
	private double[] impacts;

	@Override
	public void beforeRun() {
		super.beforeRun();
		if (solver.restarter.numRun != 0 && solver.restarter.numRun % solver.rs.cp.settingRestarts.dataResetPeriod == 0) {
			Kit.log.info("Reset of impacts");
			// for (int i = 0; i < solver.problem.variables.length; i++) impacts[i] = solver.problem.variables[i].getStaticDegree(); // TODO
			// better init ?
			Arrays.fill(impacts, 0);
		}
	}

	public Impact(SolverBacktrack solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
		alpha = 0.1;
		impacts = new double[solver.pb.variables.length];
	}

	@Override
	protected void update() {
		double impact = 1;
		if (solver.depth() > lastDepth) // the last positive decision succeeded
			for (Variable x : solver.futVars)
				impact *= x.dom.size() / (double) lastSizes[x.num];
		else
			impact = 0; // because the last positive decision failed, so a big impact (0 is the strongest impact value)
		impacts[lastVar.num] = (1 - alpha) * impacts[lastVar.num] + alpha * impact;
		assert 0 <= impact && impact <= 1 && 0 <= impacts[lastVar.num] && impacts[lastVar.num] <= 1;
	}

	@Override
	public double scoreOf(Variable x) {
		return impacts[x.num]; // note that 0 as value is the strongest impact value (we minimize)
	}

}