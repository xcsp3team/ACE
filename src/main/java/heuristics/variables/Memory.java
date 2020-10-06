/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics.variables;

import interfaces.ObserverRuns;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import variables.Variable;

public final class Memory extends HeuristicVariables implements ObserverRuns {

	@Override
	public void beforeRun() {
		nbOrdered = 0;
	}

	private int[] order;
	private int nbOrdered;
	private int posLastConflict = -1;

	public Memory(SolverBacktrack solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
		order = new int[solver.pb.variables.length];
	}

	@Override
	protected final Variable bestUnpriorityVar() {
		int pos = -1;
		for (int i = 0; i < nbOrdered; i++)
			if (!solver.pb.variables[order[i]].isAssigned()) {
				pos = i;
				break;
			}
		if (pos != -1) {
			if (posLastConflict > pos) {
				Kit.control(posLastConflict < nbOrdered);
				int vid = order[pos];
				order[pos] = order[posLastConflict];
				order[posLastConflict] = vid;
			}
			posLastConflict = pos;
		} else {
			bestScoredVariable.reset(false);
			solver.futVars.execute(x -> bestScoredVariable.update(x, scoreOptimizedOf(x)));
			pos = posLastConflict = nbOrdered;
			order[nbOrdered++] = bestScoredVariable.variable.num;
		}
		return solver.pb.variables[order[pos]];
	}

	@Override
	public double scoreOf(Variable x) {
		return x.wdeg() / x.dom.size();
	}
}
