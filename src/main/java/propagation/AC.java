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

import org.xcsp.common.Utilities;

import constraints.Constraint;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Mul2.Mul2GE;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Mul2.Mul2LE;
import solver.Solver;
import variables.Domain;
import variables.Variable;

/**
 * This is the class for (Generalized) Arc Consistency (AC). Such a propagation object solicits every constraint propagator (i.e., filtering algorithm attached
 * to a constraint) until a fixed point is reached (contrary to FC). Note that it is only when every propagator ensures AC that AC is really totally enforced on
 * the full constraint network; this information is recorded in a field. Recall that AC is the maximal level of possible filtering when constraints are treated
 * independently. <br />
 * IMPORTANT: note that, for simplicity, we use the acronym AC (and not GAC) whatever is the arity of the constraints.
 * 
 * @author Christophe Lecoutre
 */
public class AC extends Forward {

	/**********************************************************************************************
	 * Static methods
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
	 * Enforces AC on x = y + k
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            an integer
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceEQ(Domain dx, Domain dy, int k) { // x = y + k
		if (dx == dy)
			return k == 0 ? true : dx.fail();
		int minx = dx.firstValue(), miny = dy.firstValue() + k; // in miny, we take k into account
		while (minx != miny) {
			if (minx < miny) {
				if (dx.removeValuesLT(miny) == false)
					return false;
				minx = dx.firstValue();
			}
			if (miny < minx) {
				if (dy.removeValuesLT(minx - k) == false)
					return false;
				miny = dy.firstValue() + k;
			}
		}
		int maxx = dx.lastValue(), maxy = dy.lastValue() + k;
		while (maxx != maxy) {
			if (maxx > maxy) {
				if (dx.removeValuesGT(maxy) == false)
					return false;
				maxx = dx.lastValue();
			}
			if (maxy > maxx) {
				if (dy.removeValuesGT(maxx - k) == false)
					return false;
				maxy = dy.lastValue() + k;
			}
		}
		// At this stage, we know that bounds of domains (modulo k) are both equal
		int cntx = dx.size() - 1, cnty = dy.size() - 1; // -1 for directly comparing with domain distances
		boolean connexx = cntx == dx.distance(), connexy = cnty == dy.distance(); // connex means "no hole"
		if (!connexx && !connexy) {
			int a = dx.next(dx.first()), b = dy.next(dy.first()); // we start with second values
			cntx--;
			cnty--;
			int v = dx.toVal(a), w = dy.toVal(b) + k;
			while (!connexx || !connexy || v != w) {
				if (v == w) {
					a = dx.next(a);
					if (a == -1) {
						assert dy.next(b) == -1;
						return true;
					}
					b = dy.next(b);
					cntx--;
					cnty--;
				} else if (v < w) {
					if (dx.remove(a) == false)
						return false;
					a = dx.next(a);
					cntx--;
				} else {
					if (dy.remove(b) == false)
						return false;
					b = dy.next(b);
					cnty--;
				}
				v = dx.toVal(a);
				w = dy.toVal(b) + k;
				connexx = cntx == (dx.lastValue() - v);
				connexy = cnty == (dy.lastValue() + k - w);
			}
		}
		if (connexx && connexy) // domains are then similar
			return true;
		if (connexx) { // this is only in dx that we can remove some values (no possible inconsistency)
			int nToBeRemoved = dx.size() - dy.size();
			for (int a = dx.first(); a != -1 && nToBeRemoved > 0; a = dx.next(a))
				if (!dy.containsValue(dx.toVal(a) - k)) {
					dx.remove(a);
					nToBeRemoved--;
				}
		} else { // this is only in dy that we can remove some values (no possible inconsistency)
			int nToBeRemoved = dy.size() - dx.size();
			for (int b = dy.first(); b != -1 && nToBeRemoved > 0; b = dy.next(b))
				if (!dx.containsValue(dy.toVal(b) + k)) {
					dy.remove(b);
					nToBeRemoved--;
				}
		}
		return true;
	}

	/**
	 * Enforces AC on x = k - y
	 * 
	 * @param dx
	 *            the domain of x
	 * @param dy
	 *            the domain of y
	 * @param k
	 *            an integer
	 * @return false if an inconsistency is detected
	 */
	public static boolean enforceEQb(Domain dx, Domain dy, int k) { // x = k - y
		if (dx == dy)
			return k % 2 != 0 ? dx.fail() : dx.reduceToValue(k / 2);
		int minx = dx.firstValue(), miny = k - dy.lastValue(); // in miny, we take k into account
		while (minx != miny) {
			if (minx < miny) {
				if (dx.removeValuesLT(miny) == false)
					return false;
				minx = dx.firstValue();
			}
			if (miny < minx) {
				if (dy.removeValuesGT(k - minx) == false)
					return false;
				miny = k - dy.lastValue();
			}
		}
		int maxx = dx.lastValue(), maxy = k - dy.firstValue();
		while (maxx != maxy) {
			if (maxx > maxy) {
				if (dx.removeValuesGT(maxy) == false)
					return false;
				maxx = dx.lastValue();
			}
			if (maxy > maxx) {
				if (dy.removeValuesLT(k - maxx) == false)
					return false;
				maxy = k - dy.firstValue();
			}
		}
		// At this stage, we know that bounds of domains (modulo k) are both equal
		int cntx = dx.size() - 1, cnty = dy.size() - 1; // -1 for directly comparing with domain distances
		boolean connexx = cntx == dx.distance(), connexy = cnty == dy.distance(); // connex means "no hole"
		if (!connexx && !connexy) {
			int a = dx.next(dx.first()), b = dy.prev(dy.last()); // we start with second values
			cntx--;
			cnty--;
			int v = dx.toVal(a), w = k - dy.toVal(b);
			while (!connexx || !connexy || v != w) {
				if (v == w) {
					a = dx.next(a);
					if (a == -1) {
						assert dy.prev(b) == -1;
						return true;
					}
					b = dy.prev(b);
					cntx--;
					cnty--;
				} else if (v < w) {
					if (dx.remove(a) == false)
						return false;
					a = dx.next(a);
					cntx--;
				} else {
					if (dy.remove(b) == false)
						return false;
					b = dy.prev(b);
					cnty--;
				}
				v = dx.toVal(a);
				w = k - dy.toVal(b);
				connexx = cntx == (dx.lastValue() - v);
				connexy = cnty == (k - dy.firstValue() - w);
			}
		}
		if (connexx && connexy) // domains are then similar
			return true;
		if (connexx) { // this is only in dx that we can remove some values (no possible inconsistency)
			int nToBeRemoved = dx.size() - dy.size();
			for (int a = dx.first(); a != -1 && nToBeRemoved > 0; a = dx.next(a))
				if (!dy.containsValue(k - dx.toVal(a))) {
					dx.remove(a);
					nToBeRemoved--;
				}
		} else { // this is only in dy that we can remove some values (no possible inconsistency)
			int nToBeRemoved = dy.size() - dx.size();
			for (int b = dy.first(); b != -1 && nToBeRemoved > 0; b = dy.next(b))
				if (!dx.containsValue(k - dy.toVal(b))) {
					dy.remove(b);
					nToBeRemoved--;
				}
		}
		return true;
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
		if (dx == dy)
			return true;
		boolean newAlgo = true;
		if (newAlgo)
			return enforceEQ(dx, dy, 0);

		// {
		// int minx = dx.firstValue(), miny = dy.firstValue();
		// while (minx != miny) {
		// if (minx < miny) {
		// if (dx.removeValuesLT(miny) == false)
		// return false;
		// minx = dx.firstValue();
		// }
		// if (miny < minx) {
		// if (dy.removeValuesLT(minx) == false)
		// return false;
		// miny = dy.firstValue();
		// }
		// }
		// int maxx = dx.lastValue(), maxy = dy.lastValue();
		// while (maxx != maxy) {
		// if (maxx > maxy) {
		// if (dx.removeValuesGT(maxy) == false)
		// return false;
		// maxx = dx.lastValue();
		// }
		// if (maxy > maxx) {
		// if (dy.removeValuesGT(maxx) == false)
		// return false;
		// maxy = dy.lastValue();
		// }
		// }
		// // At this stage, we know that bounds of domains are both equal
		// int cntx = dx.size() - 1, cnty = dy.size() - 1; // -1 for directly comparing with domain distances
		// boolean connexx = cntx == dx.distance(), connexy = cnty == dy.distance(); // connex means "no hole"
		// if (!connexx && !connexy) {
		// int a = dx.next(dx.first()), b = dy.next(dy.first()); // we start with second values
		// cntx--;
		// cnty--;
		// int v = dx.toVal(a), w = dy.toVal(b);
		// while (!connexx || !connexy || v != w) {
		// if (v == w) {
		// a = dx.next(a);
		// if (a == -1) {
		// assert dy.next(b) == -1;
		// return true;
		// }
		// b = dy.next(b);
		// cntx--;
		// cnty--;
		// } else if (v < w) {
		// if (dx.remove(a) == false)
		// return false;
		// a = dx.next(a);
		// cntx--;
		// } else {
		// if (dy.remove(b) == false)
		// return false;
		// b = dy.next(b);
		// cnty--;
		// }
		// v = dx.toVal(a);
		// w = dy.toVal(b);
		// connexx = cntx == (dx.lastValue() - v);
		// connexy = cnty == (dy.lastValue() - w);
		// }
		// }
		// if (connexx && connexy) // domains are then similar
		// return true;
		// if (connexx) { // this is only in dx that we can remove some values (no possible inconsistency)
		// int nToBeRemoved = dx.size() - dy.size();
		// for (int a = dx.first(); a != -1 && nToBeRemoved > 0; a = dx.next(a))
		// if (!dy.containsValue(dx.toVal(a))) {
		// dx.remove(a);
		// nToBeRemoved--;
		// }
		// } else { // this is only in dy that we can remove some values (no possible inconsistency)
		// int nToBeRemoved = dy.size() - dx.size();
		// for (int b = dy.first(); b != -1 && nToBeRemoved > 0; b = dy.next(b))
		// if (!dx.containsValue(dy.toVal(b))) {
		// dy.remove(b);
		// nToBeRemoved--;
		// }
		// }
		// return true;
		// }
		{ // old algo
			Domain d1 = dx.size() <= dy.size() ? dx : dy;
			Domain d2 = d1 == dx ? dy : dx;
			if (d1.removeValuesNotIn(d2) == false)
				return false;
			if (d1.size() == d2.size())
				return true;
			assert d1.size() < d2.size();
			boolean consistent = d2.removeSurplusValuesWrt(d1);
			assert consistent && d1.size() == d2.size();
			return true;
		}
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
		Utilities.control(dx != dy, "pb");
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
	 * Indicates if AC is guaranteed for each constraint (and so, for the full constraint network), either by a generic scheme that does not require to wait for
	 * a certain number of assigned variables, or by a specific propagator.
	 */
	public final boolean guaranteed;

	/**
	 * The number of values deleted at preprocessing, by this propagation object
	 */
	public int preproRemovals;

	// public final FailedValueBasedConsistency fvbc;

	/**
	 * Builds for the specified solver a propagation object that may reach AC as level of local consistency. This is the case when all constraints guarantee to
	 * enforce AC.
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public AC(Solver solver) {
		super(solver);
		this.guaranteed = Stream.of(solver.problem.constraints).allMatch(c -> c.isGuaranteedAC());
		// this.fvbc = FailedValueBasedConsistency.buildFor(options.classForFailedValues, this)
	}

	/**
	 * Propagates constraints until reaching a fixed-point. This is AC when all constraint propagators are complete (i.e., guarantee AC). This method can be
	 * used by some subclasses enforcing a stronger level of consistency.
	 * 
	 * @return false iff an inconsistency is detected
	 */
	protected final boolean enforceAC() {
		int nBefore = solver.problem.nValueRemovals;
		queue.fill();
		if (propagate() == false)
			return false;
		preproRemovals = solver.problem.nValueRemovals - nBefore;
		assert controlAC();
		// for (Variable x : solver.problem.variables)
		// x.dom.display(0);
		return true;
	}

	/**
	 * This method is called after the specified variable has been assigned in order to propagate this event. This is AC when all constraint propagators are
	 * complete (i.e., guarantee AC). This method can be used by some subclasses enforcing a stronger level of consistency.
	 * 
	 * @param x
	 *            the variable that has just been assigned
	 * @return false iff an inconsistency is detected
	 */
	protected final boolean enforceACafterAssignment(Variable x) {
		assert x.assigned() && queue.isEmpty() : queue.size() + " " + x.assigned();
		// assert (queue.isEmpty() || this instanceof PropagationIsomorphism)
		// For the control below, note that when full AC is guaranteed, we can avoid useless filtering if the variable
		// was already singleton (no removed value at the current depth) and AC was already guaranteed.
		// TODO : the control could be more precise? (is there a constraint for which there is a problem to have
		// explicitly one less future variable?)
		if (getClass() != AC.class || x.dom.lastRemovedLevel() == solver.depth() || !guaranteed || !hasSolverPropagatedAfterLastButOneDecision()) {
			queue.add(x);
			if (propagate() == false)
				return false;
		}
		assert controlAC(true);
		// return fvbc != null ? fvbc.enforce() : true;
		return true;
	}

	/**
	 * This method is called after the specified variable has been subject to a value refutation (removal) in order to propagate this event. This is AC when all
	 * constraint propagators are complete (i.e., guarantee AC). This method can be used by some subclasses enforcing a stronger level of consistency.
	 * 
	 * @param x
	 *            the variable that has just been subject to a refutation (negative decision)
	 * @return false iff an inconsistency is detected
	 */
	protected boolean enforceACafterRefutation(Variable x) {
		if (!super.runAfterRefutation(x))
			return false;
		assert controlAC(true); // TODO also checking the objective when not in the phase following a new solution?
		return true;
	}

	@Override
	public boolean runInitially() {
		return enforceAC();
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		return enforceACafterAssignment(x);
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		return enforceACafterRefutation(x);
	}

	private boolean controlAC(boolean discardObjectiveConstraint) {
		for (Constraint c : solver.problem.constraints) {
			if (discardObjectiveConstraint && solver.problem.optimizer != null && c == solver.problem.optimizer.ctr)
				continue;
			if (c.isGuaranteedAC() && c.controlAC() == false) {
				System.out.println(c + " " + solver.problem.optimizer.ctr);
				return false;
			}
		}
		return true;
	}

	/**
	 * Returns true if all constraints of the problem guaranteeing AC are actually AC
	 */
	public final boolean controlAC() {
		return controlAC(false);
	}
}
