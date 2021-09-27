/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package propagation;

import static utility.Kit.control;

import solver.Solver;
import variables.Variable;

/**
 * An object performing a consistency stronger than GAC.
 * 
 * @author Christophe Lecoutre
 */
public abstract class StrongConsistency extends GAC {

	/**
	 * A limit in term of passes (main filtering turns)
	 */
	protected int nPassesLimit = Integer.MAX_VALUE; // TODO hard coding

	/**
	 * Indicates if the strong filtering only concerns the bounds of the variable domains
	 */
	protected boolean onlyBounds; // TODO hard coding

	/**
	 * Indicates if the strong filtering only concerns the neighbors of the event (variable)
	 */
	protected boolean onlyNeighbours; // TODO hard coding

	/**
	 * Indicates if a verbose mode is used (to display information about filtering)
	 */
	protected final int verbose;

	public StrongConsistency(Solver solver) {
		super(solver);
		this.verbose = solver.head.control.general.verbose;
		control(solver.observersOnSolving == null || solver.observersOnSolving.size() == 0);
	}

	/**
	 * Performs strong inference. The method to implement for each subclass of StrongConsistency.
	 */
	protected abstract boolean enforceStrongConsistency();

	protected boolean enforceMore() {
		// we store some statistics of the solver (because the strong consistency may change them)
		long tmpa = solver.stats.nAssignments;
		long tmpf = solver.stats.nFailedAssignments;
		long tmpb = solver.stats.nBacktracks;
		boolean consistent = enforceStrongConsistency();
		// we restore some statistics of the solver
		solver.stats.nAssignments = tmpa;
		solver.stats.nFailedAssignments = tmpf;
		solver.stats.nBacktracks = tmpb;
		return consistent;
	}

	@Override
	public boolean runInitially() {
		int nBefore = solver.problem.nValueRemovals;
		if (enforceArcConsistency() == false)
			return false;
		if (settings.strongOnlyWhenACEffective && solver.problem.nValueRemovals == nBefore)
			return true;
		if (settings.strongOnlyAtPreprocessing && solver.restarter.numRun % 60 != 0)
			return true;
		System.out.println("more");
		return enforceMore();
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		int nBefore = solver.problem.nValueRemovals;
		if (enforceArcConsistencyAfterAssignment(x) == false)
			return false;
		if (performingProperSearch || settings.strongOnlyAtPreprocessing || (settings.strongOnlyWhenACEffective && solver.problem.nValueRemovals == nBefore)
				|| (settings.strongOnlyWhenNotSingleton && x.dom.lastRemovedLevel() != solver.depth() && hasSolverPropagatedAfterLastButOneDecision()))
			return true;
		return enforceMore();
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		int nBefore = solver.problem.nValueRemovals;
		if (enforceArcConsistencyAfterRefutation(x) == false)
			return false;
		if (performingProperSearch || settings.strongOnlyAtPreprocessing || (settings.strongOnlyWhenACEffective && solver.problem.nValueRemovals == nBefore))
			return true;
		return enforceMore();
	}

}
