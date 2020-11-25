/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package learning;

import constraints.Constraint;
import dashboard.Control.SettingLearning;
import interfaces.Observers.ObserverDomainReduction;
import interfaces.Observers.ObserverRuns;
import solver.Solver;
import solver.backtrack.SolverBacktrack;
import utility.Enums.ELearningState;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public abstract class IpsRecorder implements ObserverRuns {

	public static IpsRecorder buildFor(SolverBacktrack solver) {
		if (solver.head.control.learning.state == ELearningState.EQUIVALENCE)
			return new IpsRecorderForEquivalence(solver);
		if (solver.head.control.learning.state == ELearningState.DOMINANCE)
			return new IpsRecorderForDominance(solver);
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

	public IpsRecorder(SolverBacktrack solver) {
		this.solver = solver;
		this.variables = solver.problem.variables;
		this.reductionOperator = new ReductionOperator(this);
		this.justifier = new Justifier(this);
		this.settings = solver.head.control.learning;
	}

	protected boolean mustStop() {
		return Kit.memory() > 600000000; // TODO hard coding
	}

	public abstract boolean dealWhenOpeningNode();

	public abstract void dealWhenClosingNode();

	public void displayStats() {
	}

	/**********************************************************************************************
	 * Justifier
	 *********************************************************************************************/

	public static final class Justifier implements ObserverDomainReduction {

		/**
		 * Stores which constraint is responsible of each value deletion. More precisely justifications[x][a] is either null or the constraint responsible for
		 * the deletion of the value with index a from the domain of the variable x
		 */
		public final Constraint[][] justifications;

		private final Solver solver; // redundant field

		public Justifier(IpsRecorder recorder) {
			this.solver = recorder.solver;
			if (solver.head.control.learning.state != ELearningState.NO) {
				Variable[] vars = recorder.solver.problem.variables;
				this.justifications = new Constraint[vars.length][];
				for (int i = 0; i < justifications.length; i++) {
					Domain dom = vars[i].dom;
					this.justifications[i] = new Constraint[dom.initSize()];
					for (int a = 0; a < justifications[i].length; a++)
						if (!dom.isPresent(a))
							justifications[i][a] = Constraint.TAG; // because values removed at construction time
				}
				solver.problem.observersDomainReduction.add(this);
			} else
				this.justifications = null;
		}

		@Override
		public void afterRemoval(Variable x, int a) {
			justifications[x.num][a] = solver.depth() == 0 ? Constraint.TAG : solver.propagation.currFilteringCtr;
		}

		@Override
		public void afterRemovals(Variable x, int nRemovals) {
			Constraint c = solver.depth() == 0 ? Constraint.TAG : solver.propagation.currFilteringCtr;
			for (int cnt = 0, a = x.dom.lastRemoved(); cnt < nRemovals; cnt++, a = x.dom.prevRemoved(a))
				justifications[x.num][a] = c;
		}
	}
}

//