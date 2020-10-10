/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package learning;

import interfaces.ObserverRuns;
import search.backtrack.SolverBacktrack;
import utility.Enums.ELearningState;
import utility.Kit;
import variables.Variable;

public abstract class LearnerStates implements ObserverRuns {

	public static LearnerStates buildFor(SolverBacktrack solver) {
		if (solver.rs.cp.settingLearning.state == ELearningState.EQUIVALENCE)
			return new LearnerStatesEquivalence(solver);
		if (solver.rs.cp.settingLearning.state == ELearningState.DOMINANCE)
			return new LearnerStatesDominance(solver);
		return null;
	}

	@Override
	public void afterRun() {
		displayStats();
	}

	protected int memoryLimit = 600000000;

	protected SolverBacktrack solver;

	protected Variable[] variables;

	public ReductionOperator reductionOperator;

	protected Justifier justifier;

	protected boolean stop = false;

	public int nbInferences;

	public boolean isStopped() {
		return stop;
	}

	public void clear() {}

	public LearnerStates(SolverBacktrack solver) {
		this.solver = solver;
		this.variables = solver.pb.variables;
		reductionOperator = new ReductionOperator(this);
		this.justifier = new Justifier(this);
	}

	protected boolean mustStop() {
		return Kit.getUsedMemory() > memoryLimit;
	}

	public abstract boolean dealWhenOpeningNode();

	public abstract void dealWhenClosingNode();

	public void displayStats() {}
}

//