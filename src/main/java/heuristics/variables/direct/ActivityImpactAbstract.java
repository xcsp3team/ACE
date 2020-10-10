/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics.variables.direct;

import java.util.stream.Stream;

import heuristics.variables.HeuristicVariables;
import interfaces.ObserverRuns;
import search.backtrack.SolverBacktrack;
import utility.Enums.EBranching;
import utility.Enums.ESingletonAssignment;
import utility.Kit;
import variables.Variable;

public abstract class ActivityImpactAbstract extends HeuristicVariables implements ObserverRuns {
	protected Variable lastVar; // if null, either just after pre-processing, or singleton variable
	protected int lastDepth = -1;
	protected int[] lastSizes;

	protected double alpha;

	@Override
	public void beforeRun() {
		lastVar = null;
		lastDepth = -1;
		for (int i = 0; i < solver.pb.variables.length; i++)
			lastSizes[i] = solver.pb.variables[i].dom.size();
	}

	public ActivityImpactAbstract(SolverBacktrack solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
		this.lastSizes = Stream.of(solver.pb.variables).mapToInt(x -> x.dom.size()).toArray();
		Kit.control(solver.rs.cp.settingSolving.branching == EBranching.BIN);
		Kit.control(solver.rs.cp.settingRestarts.dataResetPeriod != 0);
	}

	protected abstract void update();

	@Override
	protected Variable bestUnpriorityVar() {
		assert lastVar != null || solver.depth() > lastDepth : lastVar + " " + solver.depth() + " " + lastDepth;
		if (lastVar != null)
			update();
		bestScoredVariable.reset(true);
		solver.futVars.execute(x -> {
			if (x.dom.size() > 1 || settings.singletonAssignment != ESingletonAssignment.LAST) {
				lastSizes[x.num] = x.dom.size();
				bestScoredVariable.update(x, scoreOptimizedOf(x));
			}
		});
		if (bestScoredVariable.variable == null) {
			assert settings.singletonAssignment == ESingletonAssignment.LAST;
			return solver.futVars.first();
		}
		lastVar = bestScoredVariable.variable.dom.size() == 1 ? null : bestScoredVariable.variable;
		lastDepth = solver.depth();
		return bestScoredVariable.variable;
	}

}