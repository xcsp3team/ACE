package propagation;

import solver.Solver;
import utility.Kit;
import variables.Variable;

public abstract class StrongConsistency extends GAC {

	protected int nPassesLimit = Integer.MAX_VALUE; // TODO hard coding

	protected boolean onlyBounds, onlyNeighbours; // TODO hard coding

	protected final int verbose;

	public StrongConsistency(Solver solver) {
		super(solver);
		this.verbose = solver.head.control.general.verbose;
		Kit.control(solver.observersOnSolving == null || solver.observersOnSolving.size() == 0);
	}

	/**
	 * Performs strong inference. The method to implement for each subclass of Strong.
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
