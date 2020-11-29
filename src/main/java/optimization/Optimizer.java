package optimization;

import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Types.TypeOptimization;

import dashboard.Arguments;
import dashboard.Output;
import problem.Problem;
import solver.backtrack.SolverBacktrack;
import utility.Enums.EStopping;
import utility.Kit;
import variables.Variable;

public abstract class Optimizer { // Pilot for (mono-objective) optimization

	/**********************************************************************************************
	 * Sharing bounds between workers
	 *********************************************************************************************/

	private static Long sharedMinBound = Long.MIN_VALUE;
	private static Long sharedMaxBound = Long.MAX_VALUE;

	public final boolean possiblyUpdateSharedBounds() {
		if (!Arguments.multiThreads)
			return false;
		boolean modified = false;
		synchronized (sharedMinBound) {
			if (minBound > sharedMinBound.longValue()) {
				sharedMinBound = minBound;
				modified = true;
			}
		}
		synchronized (sharedMaxBound) {
			if (maxBound < sharedMaxBound.longValue()) {
				sharedMaxBound = maxBound;
				modified = true;
			}
		}
		return modified;
	}

	public final boolean possiblyUpdateLocalBounds() {
		if (!Arguments.multiThreads)
			return false;
		boolean modified = false;
		synchronized (sharedMinBound) {
			if (sharedMinBound.longValue() > minBound) {
				minBound = sharedMinBound.longValue();
				modified = true;
			}
		}
		synchronized (sharedMaxBound) {
			if (sharedMaxBound.longValue() < maxBound) {
				maxBound = sharedMaxBound.longValue();
				modified = true;
			}
		}
		if (modified) {
			Kit.log.fine("New Bounds updated from other workers : " + stringBounds());
			problem.solver.restarter.forceRootPropagation = true;
		}
		return modified;
	}

	/**********************************************************************************************
	 * Class
	 *********************************************************************************************/

	public final Problem problem;

	public final boolean minimization;

	public final Optimizable clb, cub, ctr;

	/**
	 * Solutions searched for must have a cost greater than or equal to this bound (valid for minimization and maximization).
	 */
	public long minBound;

	/**
	 * Solutions searched for must have a cost less than or equal to this bound (valid for minimization and maximization).
	 */
	public long maxBound;

	public Optimizer(Problem pb, TypeOptimization opt, Optimizable clb, Optimizable cub) {
		this.problem = pb;
		Kit.control(opt != null && clb != null && cub != null);
		this.minimization = opt == TypeOptimization.MINIMIZE;
		this.clb = clb;
		this.cub = cub;
		this.ctr = opt == TypeOptimization.MINIMIZE ? cub : clb; // may be null for some basic cases
		this.minBound = clb.limit();
		this.maxBound = cub.limit();
	}

	/**
	 * Returns the value of the objective, for the current complete instantiation.
	 */
	public final long value() {
		assert Variable.areAllFixed(problem.variables) && clb.objectiveValue() == cub.objectiveValue();
		// if (ctr != null)
		return cub.objectiveValue();
		// if (problem.solver.propagation instanceof LowerBoundCapability)
		// return ((LowerBoundCapability) problem.solver.propagation).getLowerBound();
		// return ((SolverLocal) problem.solver).nMinViolatedCtrs;
	}

	protected abstract void shiftLimitWhenSuccess();

	protected abstract void shiftLimitWhenFailure();

	public void afterRun() {
		Kit.control(problem.head.control.general.framework == TypeFramework.COP);
		if (problem.solver.solManager.lastSolutionRun == problem.solver.restarter.numRun) { // a better solution has been found during the last run
			if (minimization)
				maxBound = problem.solver.solManager.bestBound - 1;
			else
				minBound = problem.solver.solManager.bestBound + 1;
			possiblyUpdateLocalBounds();
			Kit.control(minBound - 1 <= maxBound || problem.head.control.optimization.ub != Long.MAX_VALUE, () -> " minB=" + minBound + " maxB=" + maxBound);
			possiblyUpdateSharedBounds();
			if (minBound > maxBound)
				problem.solver.stopping = EStopping.FULL_EXPLORATION;
			else
				shiftLimitWhenSuccess();
		} else if (problem.solver.stopping == EStopping.FULL_EXPLORATION) { // last run leads to no new solution
			if (minimization)
				minBound = cub.limit() + 1;
			else
				maxBound = clb.limit() - 1;
			Kit.log.finer("\n" + Output.COMMENT_PREFIX + "New Bounds: " + stringBounds());
			if (minBound <= maxBound) {
				problem.solver.stopping = null;
				Kit.control(problem.stuff.nValuesRemovedAtConstructionTime == 0, () -> "Not handled for the moment");
				problem.solver.restarter.forceRootPropagation = true;
				((SolverBacktrack) problem.solver).restoreProblem();
				shiftLimitWhenFailure();
			}
			if (((SolverBacktrack) problem.solver).nogoodRecorder != null)
				((SolverBacktrack) problem.solver).nogoodRecorder.reset();
		}
	}

	protected void shiftLimit(long offset) {
		Kit.control(0 <= offset && minBound + offset <= maxBound, () -> "offset " + offset + " minBound " + minBound + " maxBound " + maxBound);
		long newLimit = minimization ? maxBound - offset : minBound + offset;
		Kit.log.finer(Output.COMMENT_PREFIX + "New Limit: " + newLimit + "\n");
		ctr.limit(newLimit);
	}

	public final String stringBounds() {
		return (minBound == Long.MIN_VALUE ? "-infty" : minBound) + ".." + (maxBound == Long.MAX_VALUE ? "+infty" : maxBound);
	}

	@Override
	public String toString() {
		return (minimization ? TypeOptimization.MINIMIZE : TypeOptimization.MAXIMIZE).shortName() + " " + ctr.toString();
	}

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	// TODO problem when incremental with STR2 and CT for Increasing and Dichotomic
	// It seems that SVal is not correctly updated

	public static final class OptimizerDecreasing extends Optimizer {
		// Assuming minimization (similar observation for maximization):
		// with this strategy, the limit of clb never changes
		// so, the constraint makes sense (i.e. filters) only if -lb is set by the user
		// otherwise, it does not matter because the constraint is entailed

		public OptimizerDecreasing(Problem pb, TypeOptimization opt, Optimizable clb, Optimizable cub) {
			super(pb, opt, clb, cub);
		}

		@Override
		protected void shiftLimitWhenSuccess() {
			if (minimization)
				cub.limit(maxBound);
			else
				clb.limit(minBound);
		}

		@Override
		protected void shiftLimitWhenFailure() {
			throw new AssertionError("should not be called");
		}
	}

	public static final class OptimizerIncreasing extends Optimizer {

		boolean first = true;

		public OptimizerIncreasing(Problem pb, TypeOptimization opt, Optimizable clb, Optimizable cub) {
			super(pb, opt, clb, cub);
		}

		@Override
		protected void shiftLimitWhenSuccess() {
			if (first) { // we now attempt to find optimality by increasingly updating the bounds (if minimization)
				if (minimization)
					cub.limit(minBound); // so limits are the same for clb and cub
				else
					clb.limit(maxBound);
				first = false;
			} else
				throw new AssertionError("should never be called again");
		}

		@Override
		protected void shiftLimitWhenFailure() {
			if (minimization) {
				clb.limit(minBound);
				cub.limit(minBound);
			} else {
				clb.limit(maxBound);
				cub.limit(maxBound);
			}
		}
	}

	// java ace /home/lecoutre/instances/XCSP18v2/allInstances/Fapp/Fapp-m2s/Fapp-m2s-01-0200_c18.xml.lzma -os=dichotomic -positive=str2 PROBLEM
	// but STR1 ok
	// if decremental set to false in STRoptimized, STR2 ok (but not CT that need decremental); why?
	public static final class OptimizerDichotomic extends Optimizer {

		public OptimizerDichotomic(Problem pb, TypeOptimization opt, Optimizable clb, Optimizable cub) {
			super(pb, opt, clb, cub);
		}

		@Override
		protected void shiftLimitWhenSuccess() {
			shiftLimit((maxBound - minBound) / 2);
		}

		@Override
		protected void shiftLimitWhenFailure() {
			shiftLimit((maxBound - minBound) / 2);
		}
	}

	// public static final class OptimizerBasic extends Optimizer {
	//
	// public final String optimizationExpression;
	//
	// public OptimizerBasic(Problem pb, String optimizationExpression) {
	// super(pb, TypeOptimization.MINIMIZE, null);
	// this.optimizationExpression = optimizationExpression;
	// }
	//
	// @Override
	// protected void shiftLimitWhenSuccess() {
	// }
	//
	// @Override
	// protected void shiftLimitWhenFailure() {
	// }
	//
	// @Override
	// public String toString() {
	// return (minimization ? TypeOptimization.MINIMIZE : TypeOptimization.MAXIMIZE).shortName() + " " + optimizationExpression;
	// }
	// }

}
