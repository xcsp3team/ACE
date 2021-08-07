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
		Kit.control(solver.observersSearch == null || solver.observersSearch.size() == 0);
	}

	/**
	 * Performs strong inference. The method to implement for each subclass of Strong.
	 */
	protected abstract boolean enforceStrongConsistency();

	protected boolean enforceMore() {
		solver.stats.store();
		boolean consistent = enforceStrongConsistency();
		solver.stats.restore();
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
