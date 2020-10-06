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

public class Activity extends ActivityImpactAbstract {
	private double[] activities;

	@Override
	public void beforeRun() {
		super.beforeRun();
		if (solver.restarter.numRun != 0 && solver.restarter.numRun % solver.rs.cp.restarting.dataResetPeriod == 0) {
			Kit.log.info("Reset of activities");
			Arrays.fill(activities, 0);
		}
	}

	public Activity(SolverBacktrack solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
		alpha = 0.99; // alpha as an aging decay
		activities = new double[solver.pb.variables.length];
	}

	@Override
	protected void update() {
		if (solver.depth() > lastDepth) { // the last positive decision succeeded
			solver.futVars.execute(x -> activities[x.num] = x.dom.size() != lastSizes[x.num] ? activities[x.num] + 1 : activities[x.num] * alpha);
		} else
			activities[lastVar.num] += 2; // because the last positive decision failed, so a big activity
	}

	@Override
	public double scoreOf(Variable x) {
		return -activities[x.num] / x.dom.size(); // minus because we have to minimize
	}

}