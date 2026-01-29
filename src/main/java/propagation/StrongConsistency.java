/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
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
 * An object performing a consistency stronger than AC.
 * 
 * @author Christophe Lecoutre
 */
public abstract class StrongConsistency extends AC {

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
	 * 
	 * @return false if an inconsistency is detected
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
		if (enforceAC() == false)
			return false;
		if (options.strongAC && solver.problem.nValueRemovals == nBefore)
			return true;
		if (options.strongOnce && (solver.restarter.numRun + 1) % 60 != 0)
			return true;
		// Kit.log.config("more");
		return enforceMore();
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		int nBefore = solver.problem.nValueRemovals;
		if (enforceACafterAssignment(x) == false)
			return false;
		if (performingProperSearch || options.strongOnce || (options.strongAC && solver.problem.nValueRemovals == nBefore)
				|| (x.dom.lastRemovedLevel() != solver.depth() && hasSolverPropagatedAfterLastButOneDecision()))
			// the last part of condition means that no value has been deleted by the assignment and propagation was
			// previously made
			return true;
		return enforceMore();
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		int nBefore = solver.problem.nValueRemovals;
		if (enforceACafterRefutation(x) == false)
			return false;
		if (performingProperSearch || options.strongOnce || (options.strongAC && solver.problem.nValueRemovals == nBefore))
			return true;
		return enforceMore();
	}

}
