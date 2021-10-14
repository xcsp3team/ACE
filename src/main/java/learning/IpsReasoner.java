/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package learning;

import constraints.Constraint;
import dashboard.Control.OptionsLearning;
import interfaces.Observers.ObserverOnConflicts;
import interfaces.Observers.ObserverOnRemovals;
import interfaces.Observers.ObserverOnRuns;
import solver.Solver;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public abstract class IpsReasoner implements ObserverOnRuns, ObserverOnConflicts {

	/**
	 * Builds and returns an object used for recording and reasoning with Inconsistent Partial States (IPSs), or null.
	 * 
	 * @param solver
	 *            the solver to which the built reasoner will be attached
	 * @return an object recording and reasoning with IPSs, or null
	 */
	public static IpsReasoner buildFor(Solver solver) {
		if (solver.head.control.learning.ips == LearningIps.EQUIVALENCE)
			return new IpsReasonerEquivalence(solver);
		if (solver.head.control.learning.ips == LearningIps.DOMINANCE)
			return new IpsReasonerDominance(solver);
		return null;
	}

	public enum LearningIps {
		NO, EQUIVALENCE, DOMINANCE;
	}

	/**********************************************************************************************
	 * Implementing Interfaces
	 *********************************************************************************************/

	@Override
	public void afterRun() {
		displayStats();
	}

	@Override
	public void whenWipeout(Constraint c, Variable x) {
	}

	@Override
	public void whenBacktrack() {
		whenClosingNode();
	}

	/**********************************************************************************************
	 * Inner class: Explainer
	 *********************************************************************************************/

	public final class Explainer implements ObserverOnRemovals {

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

		/**
		 * Stores which constraint is responsible of each value deletion. More precisely justifications[x][a] is either
		 * null or the constraint responsible for the deletion of the value index a from the domain of the variable x
		 */
		public final Constraint[][] justifications;

		/**
		 * Builds an object storing the explanation of any value removal
		 */
		public Explainer() {
			this.justifications = new Constraint[variables.length][];
			for (int i = 0; i < justifications.length; i++) {
				Domain dom = variables[i].dom;
				this.justifications[i] = new Constraint[dom.initSize()];
				for (int a = 0; a < justifications[i].length; a++)
					if (!dom.contains(a))
						justifications[i][a] = Constraint.TAG; // because values removed at construction time
			}
		}
	}

	/**********************************************************************************************
	 * Class Members
	 *********************************************************************************************/

	/**
	 * The solver to which this object is attached
	 */
	protected final Solver solver;

	/**
	 * The variables of the problem (redundant field)
	 */
	protected final Variable[] variables;

	/**
	 * The object embedding so-called reduction operators, which allow us to build IPSs
	 */
	public final IpsExtractor extractor;

	/**
	 * The object storing the explanation (as a constraint) of every value removal
	 */
	public final Explainer explainer;

	/**
	 * The options concerning learning
	 */
	protected final OptionsLearning options;

	public boolean stopped = false;

	public int nInferences;

	/**
	 * Builds an object recording and reasoning with IPSs for the specified solver
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public IpsReasoner(Solver solver) {
		this.solver = solver;
		this.variables = solver.problem.variables;
		this.extractor = new IpsExtractor(this);
		this.explainer = new Explainer();
		this.options = solver.head.control.learning;
	}

	protected boolean mustStop() {
		return Kit.memory() > 600000000; // TODO hard coding
	}

	/**
	 * Called when a new node of the search tree is opened
	 * 
	 * @return false if an inconsistency is detected
	 */
	public abstract boolean whenOpeningNode();

	/**
	 * Called when the current node of the search tree is closed (i.e., when backtracking)
	 */
	public abstract void whenClosingNode();

	public void displayStats() {
	}

}

//