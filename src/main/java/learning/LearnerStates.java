/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package learning;

import dashboard.ControlPanel.SettingLearning;
import interfaces.ObserverRuns;
import search.backtrack.SolverBacktrack;
import utility.Enums.ELearningState;
import utility.Kit;
import variables.Variable;

public abstract class LearnerStates implements ObserverRuns {

	public static LearnerStates buildFor(SolverBacktrack solver) {
		if (solver.head.control.settingLearning.state == ELearningState.EQUIVALENCE)
			return new LearnerStatesEquivalence(solver);
		if (solver.head.control.settingLearning.state == ELearningState.DOMINANCE)
			return new LearnerStatesDominance(solver);
		return null;
	}

	@Override
	public void afterRun() {
		displayStats();
	}

	protected final SolverBacktrack solver;

	protected final Variable[] variables;

	public final ReductionOperator reductionOperator;

	protected final Justifier justifier;

	protected final SettingLearning settings;

	public boolean stopped = false;

	public int nInferences;

	public LearnerStates(SolverBacktrack solver) {
		this.solver = solver;
		this.variables = solver.problem.variables;
		this.reductionOperator = new ReductionOperator(this);
		this.justifier = new Justifier(this);
		this.settings = solver.head.control.settingLearning;
	}

	protected boolean mustStop() {
		return Kit.memory() > 600000000; // TODO hard coding
	}

	public abstract boolean dealWhenOpeningNode();

	public abstract void dealWhenClosingNode();

	public void displayStats() {
	}
}

//