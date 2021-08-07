package propagation;

import java.util.stream.Stream;

import solver.Solver;
import variables.Variable;

/**
 * This propagation object solicits every constraint propagator until a fixed point is reached (contrary to FC). If every propagator ensures GAC, we then
 * enforce GAC. This information is recorded in the field 'guaranteed'.
 * 
 * @author Christophe Lecoutre
 */
public class GAC extends Forward {

	/**
	 * Indicates if GAC is guaranteed for each constraint, either by a generic scheme that does not requires to wait for a certain number of assigned, or by a
	 * specific propagator.
	 */
	public final boolean guaranteed;

	/**
	 * The number of deleted values at preprocessing, by AC.
	 */
	public int nPreproValueRemovals;

	// public final FailedValueBasedConsistency fvbc;

	public GAC(Solver solver) {
		super(solver);
		this.guaranteed = Stream.of(solver.problem.constraints).allMatch(c -> c.isGuaranteedAC());
		// this.fvbc = FailedValueBasedConsistency.buildFor(settings.classForFailedValues, this)
	}

	/**
	 * Propagates constraints until reaching a fixed-point. This is (G)AC iff all constraint propagators are complete. This method can be useful by some
	 * subclasses enforcing a stronger level of consistency.
	 * 
	 * @return false iff an inconsistency is detected
	 */
	protected final boolean enforceArcConsistency() {
		int nBefore = solver.problem.nValueRemovals;
		queue.fill();
		boolean consistent = propagate();
		nPreproValueRemovals = solver.problem.nValueRemovals - nBefore;
		if (!consistent)
			return false;
		assert controlArcConsistency();
		return true;
	}

	@Override
	public boolean runInitially() {
		return enforceArcConsistency();
	}

	/**
	 * This method is called after the specified variable has been assigned in order to propagate this event. This is (G)AC iff all constraint propagators are
	 * complete. This method can be useful by some subclasses enforcing a stronger level of consistency.
	 * 
	 * @param x
	 *            the variable that has just been assigned
	 * @return false iff an inconsistency is detected
	 */
	protected final boolean enforceArcConsistencyAfterAssignment(Variable x) {
		assert x.assigned() && queue.isEmpty() : queue.size() + " " + x.assigned(); // (queue.isEmpty() || this instanceof PropagationIsomorphism)
		// when pure GAC, we can avoid useless filtering if the variable was already singleton (no removed value at the current depth) and GAC was already
		// guaranteed. TODO : the control could be more precise (is there a constraint for which there is a problem to have explicitly one less future
		// variable?)
		if (getClass() != GAC.class || x.dom.lastRemovedLevel() == solver.depth() || !guaranteed || !hasSolverPropagatedAfterLastButOneDecision()) {
			queue.add(x);
			if (propagate() == false)
				return false;
		}
		assert controlArcConsistency();
		// return fvbc != null ? fvbc.enforce() : true;
		return true;
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		return enforceArcConsistencyAfterAssignment(x);
	}

	/**
	 * This method is called after the specified variable has been subject to a value refutation (removal) in order to propagate this event. This is (G)AC iff
	 * all constraint propagators are complete. This method can be useful by some subclasses enforcing a stronger level of consistency.
	 * 
	 * @param x
	 *            the variable that has just been subject to a refutation (negative decision)
	 * @return false iff an inconsistency is detected
	 */
	protected boolean enforceArcConsistencyAfterRefutation(Variable x) {
		if (!super.runAfterRefutation(x))
			return false;
		// TODO also checking the objective when not in the phase following a new solution
		assert !guaranteed || Stream.of(solver.problem.constraints)
				.allMatch(c -> solver.problem.optimizer != null && c == solver.problem.optimizer.ctr || c.controlArcConsistency());
		// assert controlArcConsistency();
		return true;
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		return enforceArcConsistencyAfterRefutation(x);
	}

	public final boolean controlArcConsistency() {
		return !guaranteed || Stream.of(solver.problem.constraints).allMatch(c -> c.controlArcConsistency());
	}
}
