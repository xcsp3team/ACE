/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package optimization;

import static org.xcsp.common.Types.TypeFramework.COP;
import static org.xcsp.common.Types.TypeOptimization.MAXIMIZE;
import static org.xcsp.common.Types.TypeOptimization.MINIMIZE;
import static solver.Solver.Stopping.FULL_EXPLORATION;
import static utility.Kit.control;

import java.util.stream.Stream;

import org.xcsp.common.Types.TypeOptimization;

import dashboard.Input;
import interfaces.Observers.ObserverOnRuns;
import problem.Problem;
import utility.Kit;

/**
 * A pilot for dealing with (mono-objective) optimization. Subclasses define various strategies to conduct search toward
 * optimality.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Optimizer implements ObserverOnRuns {

	/**
	 * Currently, three strategies to conduct search toward optimality
	 */
	public static enum OptimizationStrategy {
		INCREASING, DECREASING, DICHOTOMIC;
	}

	/**********************************************************************************************
	 * Implementing interface
	 *********************************************************************************************/

	@Override
	public final void afterRun() {
		control(problem.framework == COP);
		if (problem.solver.solutions.lastRun == problem.solver.restarter.numRun) { // a better solution has been found
																					// during the last run
			if (minimization) {
				maxBound = problem.solver.solutions.bestBound - 1;
				cub.limit(maxBound);
			} else {
				minBound = problem.solver.solutions.bestBound + 1;
				clb.limit(minBound);
			}
			possiblyUpdateLocalBounds();
			control(minBound - 1 <= maxBound || problem.head.control.optimization.ub != Long.MAX_VALUE, () -> " minB=" + minBound + " maxB=" + maxBound);
			possiblyUpdateSharedBounds();
			if (minBound > maxBound)
				problem.solver.stopping = FULL_EXPLORATION;
			else
				shiftLimitWhenSuccess();
		} else if (problem.solver.stopping == FULL_EXPLORATION) { // last run leads to no new solution
			boolean clb_changed = clb.limit() != minBound, cub_changed = cub.limit() != maxBound;
			control(!clb_changed || !cub_changed);
			if (!clb_changed && !cub_changed) { // classical mode
				if (minimization) {
					minBound = cub.limit() + 1;
					clb.limit(minBound);
				} else {
					maxBound = clb.limit() - 1;
					cub.limit(maxBound);
				}
			} else if (cub_changed) { // aggressive mode (the upper bound was reduced)
				minBound = cub.limit() + 1;
				clb.limit(minBound);
				cub.limit(maxBound);
			} else { // aggressive mode (the lower bound was reduced)
				maxBound = clb.limit() - 1;
				cub.limit(maxBound);
				clb.limit(minBound);
			}
			if (minBound <= maxBound) { // we continue after resetting
				problem.solver.stopping = null;
				control(problem.features.nValuesRemovedAtConstructionTime == 0, () -> "Not handled for the moment");
				problem.solver.restarter.forceRootPropagation = true;
				problem.solver.restoreProblem();
				if (problem.solver.nogoodReasoner != null)
					problem.solver.nogoodReasoner.reset();
				shiftLimitWhenFailure();
			}
		}
	}

	/**********************************************************************************************
	 * Class
	 *********************************************************************************************/

	/**
	 * THe problem to which this object is attached
	 */
	public final Problem problem;

	/**
	 * indicates if one must minimize (otherwise, maximize)
	 */
	public final boolean minimization;

	/**
	 * the constraint ensuring that minimal bound (lower bound) of the optimization bounding interval is respected; may
	 * be useless.
	 */
	public final Optimizable clb;

	/**
	 * the constraint ensuring that maximal bound (upper bound) of the optimization bounding interval is respected; may
	 * be useless.
	 */
	public final Optimizable cub;

	/**
	 * the leading (main) constraint for optimization; it is either clb or cub
	 */
	public final Optimizable ctr;

	/**
	 * solutions searched for must have a cost greater than or equal to this bound (valid for both minimization and
	 * maximization).
	 */
	public long minBound;

	/**
	 * solutions searched for must have a cost less than or equal to this bound (valid for both minimization and
	 * maximization).
	 */
	public long maxBound;

	public Optimizer(Problem pb, TypeOptimization opt, Optimizable clb, Optimizable cub) {
		this.problem = pb;
		control(opt != null && clb != null && cub != null);
		this.minimization = opt == MINIMIZE;
		this.clb = clb;
		this.cub = cub;
		this.ctr = opt == MINIMIZE ? cub : clb; // the leading constraint (used at some places in other classes)
		this.minBound = clb.limit();
		this.maxBound = cub.limit();
	}

	/**
	 * Returns the value of the problem objective, computed with respect to the current complete instantiation
	 * 
	 * @return the current value of the problem objective
	 */
	public final long value() {
		assert Stream.of(problem.variables).allMatch(x -> x.dom.size() == 1) && clb.objectiveValue() == cub.objectiveValue();
		return cub.objectiveValue();
	}

	protected abstract void shiftLimitWhenSuccess();

	protected abstract void shiftLimitWhenFailure();

	public final String stringBounds() {
		return (minBound == Long.MIN_VALUE ? "-infty" : minBound) + ".." + (maxBound == Long.MAX_VALUE ? "+infty" : maxBound);
	}

	@Override
	public String toString() {
		return minimization ? MINIMIZE.shortName() + " " + cub : MAXIMIZE.shortName() + " " + clb.toString();
	}

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	// TODO problem when incremental is used with STR2 and CT for Increasing and Dichotomic strategies
	// It seems that SVal is not correctly updated
	// java ace Fapp-m2s-01-0200_c18.xml.lzma -os=dichotomic -positive=str2 PROBLEM but STR1 ok ; if decremental set to
	// false in STRoptimized,
	// STR2 ok (but not CT that need decremental); why?

	/**
	 * An optimization strategy based on decreasingly updating the maximal bound (assuming minimization) whenever a
	 * solution is found; this is related to branch and bound (and related to ramp-down strategy).
	 */
	public static final class OptimizerDecreasing extends Optimizer {
		// Assuming minimization (similar observation for maximization):
		// with this strategy, the limit of clb never changes, so, the constraint makes sense (i.e. filters) only if -lb
		// is set by the user
		// otherwise, it does not matter because the constraint is entailed

		public OptimizerDecreasing(Problem pb, TypeOptimization opt, Optimizable clb, Optimizable cub) {
			super(pb, opt, clb, cub);
		}

		@Override
		protected void shiftLimitWhenSuccess() {
			// nothing to do
		}

		@Override
		protected void shiftLimitWhenFailure() {
			throw new AssertionError("should not be called");
		}
	}

	/**
	 * An optimization strategy based on increasingly updating the minimal bound (assuming minimization); this is
	 * sometimes called iterative optimization (or ramp-up strategy).
	 */
	public static final class OptimizerIncreasing extends Optimizer {

		boolean first = true;

		public OptimizerIncreasing(Problem pb, TypeOptimization opt, Optimizable clb, Optimizable cub) {
			super(pb, opt, clb, cub);
		}

		@Override
		protected void shiftLimitWhenSuccess() {
			if (first) { // we now attempt to find optimality by increasingly updating the bounds (if minimization)
				if (minimization)
					cub.limit(minBound); // so limits are now the same for clb and cub
				else
					clb.limit(maxBound); // so limits are now the same for clb and cub
				first = false;
			} else
				throw new AssertionError("should never be called again");
		}

		@Override
		protected void shiftLimitWhenFailure() {
			if (minimization)
				cub.limit(minBound); // we keep same limits for clb and cub
			else
				clb.limit(maxBound); // we keep same limits for clb and cub
		}
	}

	/**
	 * An optimization strategy based on a dichotomic reduction of the bounding interval. <br />
	 */
	public static final class OptimizerDichotomic extends Optimizer {

		public OptimizerDichotomic(Problem pb, TypeOptimization opt, Optimizable clb, Optimizable cub) {
			super(pb, opt, clb, cub);
		}

		@Override
		protected void shiftLimitWhenSuccess() {
			long offset = (maxBound - minBound) / 2;
			if (minimization)
				cub.limit(maxBound - offset);
			else
				clb.limit(minBound + offset);
		}

		@Override
		protected void shiftLimitWhenFailure() {
			long offset = (maxBound - minBound) / 2;
			if (minimization)
				cub.limit(maxBound - offset);
			else
				clb.limit(minBound + offset);
		}
	}

	/**********************************************************************************************
	 * Sharing bounds between workers (when in portfolio mode)
	 *********************************************************************************************/

	private static class MyLong {
		Long value;

		MyLong(Long v) {
			this.value = v;
		}
	}

	private static MyLong sharedMinBound = new MyLong(Long.MIN_VALUE);

	private static MyLong sharedMaxBound = new MyLong(Long.MAX_VALUE);

	public final boolean possiblyUpdateSharedBounds() {
		if (!Input.portfolio)
			return false;
		boolean modified = false;
		synchronized (sharedMinBound) {
			if (minBound > sharedMinBound.value) {
				sharedMinBound.value = minBound;
				modified = true;
			}
		}
		synchronized (sharedMaxBound) {
			if (maxBound < sharedMaxBound.value) {
				sharedMaxBound.value = maxBound;
				modified = true;
			}
		}
		return modified;
	}

	public final boolean possiblyUpdateLocalBounds() {
		if (!Input.portfolio)
			return false;
		boolean modified = false;
		synchronized (sharedMinBound) {
			if (sharedMinBound.value > minBound) {
				minBound = sharedMinBound.value;
				modified = true;
			}
		}
		synchronized (sharedMaxBound) {
			if (sharedMaxBound.value < maxBound) {
				maxBound = sharedMaxBound.value;
				modified = true;
			}
		}
		if (modified) {
			Kit.log.fine("New Bounds updated from other workers : " + stringBounds());
			problem.solver.restarter.forceRootPropagation = true;
		}
		return modified;
	}
}
