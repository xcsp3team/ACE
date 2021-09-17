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

import java.util.stream.Stream;

import constraints.Constraint;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Mul2.Mul2GE;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Mul2.Mul2LE;
import solver.Solver;
import variables.Domain;
import variables.Variable;

/**
 * This propagation object solicits every constraint propagator (i.e., filtering algorithm attached to a constraint)
 * until a fixed point is reached (contrary to FC). Note that it is only when every propagator ensures GAC (Generalized
 * Arc Consistency) that GAC is really enforced completely on the full constraint network; this information is recorded
 * in a field. Recall that GAC is the maximal level of possible filtering when constraints are treated independently.
 * 
 * @author Christophe Lecoutre
 */
public class GAC extends Forward {

	/**********************************************************************************************
	 * Static members
	 *********************************************************************************************/

	/**
	 * Enforces AC on x < y
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceLT(Domain dx, Domain dy) { // x < y
		return dx.removeValuesGE(dy.lastValue()) && dy.removeValuesLE(dx.firstValue());
	}

	/**
	 * Enforces AC on x < y + k
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            a constant
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceLT(Domain dx, Domain dy, int k) { // x < y + k
		return dx.removeValuesGE(dy.lastValue() + k) && dy.removeValuesLE(dx.firstValue() - k);
	}

	/**
	 * Enforces AC on x <= y
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceLE(Domain dx, Domain dy) { // x <= y
		return dx.removeValuesGT(dy.lastValue()) && dy.removeValuesLT(dx.firstValue());
	}

	/**
	 * Enforces AC on x <= y + k
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            a constant
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceLE(Domain dx, Domain dy, int k) { // x <= y + k
		return dx.removeValuesGT(dy.lastValue() + k) && dy.removeValuesLT(dx.firstValue() - k);
	}

	/**
	 * Enforces AC on x >= y
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceGE(Domain dx, Domain dy) { // x >= y
		return dx.removeValuesLT(dy.firstValue()) && dy.removeValuesGT(dx.lastValue());
	}

	/**
	 * Enforces AC on x >= y + k
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            a constant
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceGE(Domain dx, Domain dy, int k) { // x >= y + k
		return dx.removeValuesLT(dy.firstValue() + k) && dy.removeValuesGT(dx.lastValue() - k);
	}

	/**
	 * Enforces AC on x > y
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceGT(Domain dx, Domain dy) { // x > y
		return dx.removeValuesLE(dy.firstValue()) && dy.removeValuesGE(dx.lastValue());
	}

	/**
	 * Enforces AC on x > y + k
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            a constant
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceGT(Domain dx, Domain dy, int k) { // x > y + k
		return dx.removeValuesLE(dy.firstValue() + k) && dy.removeValuesGE(dx.lastValue() - k);
	}

	/**
	 * Enforces AC on x = y
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceEQ(Domain dx, Domain dy) { // x = y
		if (dx.removeValuesNotIn(dy) == false)
			return false;
		if (dx.size() == dy.size())
			return true;
		assert dx.size() < dy.size();
		boolean consistent = dy.removeValuesNotIn(dx);
		assert consistent && dx.size() == dy.size();
		return true;
	}

	/**
	 * Enforces AC on x != y
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceNE(Domain dx, Domain dy) { // x != y
		if (dx.size() == 1)
			return dy.removeValueIfPresent(dx.singleValue());
		if (dy.size() == 1)
			return dx.removeValueIfPresent(dy.singleValue());
		return true;
	}

	/**
	 * Enforces AC on x + y <= k
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            a constant
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceAddLE(Domain dx, Domain dy, int k) { // x + y <= k
		return dx.removeValuesGT(k - dy.firstValue()) && dy.removeValuesGT(k - dx.firstValue());
	}

	/**
	 * Enforces AC on x + y >= k
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            a constant
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceAddGE(Domain dx, Domain dy, int k) { // x + y >= k
		return dx.removeValuesLT(k - dy.lastValue()) && dy.removeValuesLT(k - dx.lastValue());
	}

	/**
	 * Enforces AC on x * y <= k
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            a constant
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceMulLE(Domain dx, Domain dy, int k) { // x * y <= k
		return Mul2LE.revise(dx, dy, k) && Mul2LE.revise(dy, dx, k);
	}

	/**
	 * Enforces AC on x * y >= k
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            a constant
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceMulGE(Domain dx, Domain dy, int k) { // x * y >= k
		return Mul2GE.revise(dx, dy, k) && Mul2GE.revise(dy, dx, k);
	}

	/**
	 * Enforces AC on x / y <= k
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            a constant
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceDivLE(Domain dx, Domain dy, int k) { // x / y <= k
		return dx.removeValuesNumeratorsGT(k, dy.lastValue()) && dy.removeValuesDenominatorsGT(k, dx.firstValue());
	}

	/**
	 * Enforces AC on x / y >= k
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            a constant
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceDivGE(Domain dx, Domain dy, int k) { // x / y >= k
		return dx.removeValuesNumeratorsLT(k, dy.firstValue()) && dy.removeValuesDenominatorsLT(k, dx.lastValue());
	}

	/**********************************************************************************************
	 * Fields and Methods
	 *********************************************************************************************/

	/**
	 * Indicates if GAC is guaranteed for each constraint (and so, for the full constraint network), either by a generic
	 * scheme that does not require to wait for a certain number of assigned variables, or by a specific propagator.
	 */
	public final boolean guaranteed;

	/**
	 * The number of values deleted at preprocessing, by this propagation object
	 */
	public int preproRemovals;

	// public final FailedValueBasedConsistency fvbc;

	/**
	 * Builds for the specified solver a propagation object that may reach GAC as level of local consistency. This is
	 * the case when all constraints guarantee to enforce GAC.
	 * 
	 * @param solver
	 *            the solver to which this propagation object is attached
	 */
	public GAC(Solver solver) {
		super(solver);
		this.guaranteed = Stream.of(solver.problem.constraints).allMatch(c -> c.isGuaranteedAC());
		// this.fvbc = FailedValueBasedConsistency.buildFor(settings.classForFailedValues, this)
	}

	/**
	 * Propagates constraints until reaching a fixed-point. This is GAC when all constraint propagators are complete
	 * (i.e., guarantee GAC). This method can be used by some subclasses enforcing a stronger level of consistency.
	 * 
	 * @return false iff an inconsistency is detected
	 */
	protected final boolean enforceArcConsistency() {
		int nBefore = solver.problem.nValueRemovals;
		queue.fill();
		if (propagate() == false)
			return false;
		preproRemovals = solver.problem.nValueRemovals - nBefore;
		assert controlGAC();
		return true;
	}

	/**
	 * This method is called after the specified variable has been assigned in order to propagate this event. This is
	 * GAC when all constraint propagators are complete (i.e., guarantee GAC). This method can be used by some
	 * subclasses enforcing a stronger level of consistency.
	 * 
	 * @param x
	 *            the variable that has just been assigned
	 * @return false iff an inconsistency is detected
	 */
	protected final boolean enforceArcConsistencyAfterAssignment(Variable x) {
		assert x.assigned() && queue.isEmpty() : queue.size() + " " + x.assigned();
		// (queue.isEmpty() || this instanceof PropagationIsomorphism)
		// For the control below, note that when full GAC is guaranteed, we can avoid useless filtering if the variable
		// was already singleton (no removed value at the current depth) and GAC was already guaranteed.
		// TODO : the control could be more precise? (is there a constraint for which there is a problem to have
		// explicitly one less future variable?)
		if (getClass() != GAC.class || x.dom.lastRemovedLevel() == solver.depth() || !guaranteed || !hasSolverPropagatedAfterLastButOneDecision()) {
			queue.add(x);
			if (propagate() == false)
				return false;
		}
		assert controlGAC();
		// return fvbc != null ? fvbc.enforce() : true;
		return true;
	}

	/**
	 * This method is called after the specified variable has been subject to a value refutation (removal) in order to
	 * propagate this event. This is GAC when all constraint propagators are complete (i.e., guarantee GAC). This method
	 * can be used by some subclasses enforcing a stronger level of consistency.
	 * 
	 * @param x
	 *            the variable that has just been subject to a refutation (negative decision)
	 * @return false iff an inconsistency is detected
	 */
	protected boolean enforceArcConsistencyAfterRefutation(Variable x) {
		if (!super.runAfterRefutation(x))
			return false;
		assert controlGAC(true); // TODO also checking the objective when not in the phase following a new solution?
		return true;
	}

	@Override
	public boolean runInitially() {
		return enforceArcConsistency();
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		return enforceArcConsistencyAfterAssignment(x);
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		return enforceArcConsistencyAfterRefutation(x);
	}

	private boolean controlGAC(boolean discardObjectiveConstraint) {
		for (Constraint c : solver.problem.constraints) {
			if (discardObjectiveConstraint && solver.problem.optimizer != null && c == solver.problem.optimizer.ctr)
				continue;
			if (c.isGuaranteedAC() && c.controlGAC() == false)
				return false;
		}
		return true;
	}

	/**
	 * Returns true if all constraints of the problem guaranteeing GAC are actually GAC
	 */
	public final boolean controlGAC() {
		return controlGAC(false);
	}
}
