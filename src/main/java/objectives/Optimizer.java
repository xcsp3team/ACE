package objectives;

import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Types.TypeOptimization;

import dashboard.Arguments;
import dashboard.Output;
import interfaces.LowerBoundCapability;
import interfaces.Optimizable;
import problem.Problem;
import search.backtrack.SolverBacktrack;
import search.local.SolverLocal;
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
			pb.solver.restarter.forceRootPropagation = true;
		}
		return modified;
	}

	/**********************************************************************************************
	 * Class
	 *********************************************************************************************/

	public final Problem pb;

	public final boolean minimization;

	public final Optimizable ctr;

	/**
	 * Solutions searched for must have a cost greater than or equal to this bound (valid for minimization and maximization).
	 */
	protected long minBound;

	/**
	 * Solutions searched for must have a cost less than or equal to this bound (valid for minimization and maximization).
	 */
	protected long maxBound;

	public Optimizer(Problem pb, TypeOptimization opt, Optimizable ctr) {
		this.pb = pb;
		Kit.control(opt != null);
		this.minimization = opt == TypeOptimization.MINIMIZE;
		this.ctr = ctr; // may be null for some basic cases
		this.minBound = Math.max(pb.head.control.settingOptimization.lowerBound, ctr != null ? ctr.minComputableObjectiveValue() : Long.MIN_VALUE);
		this.maxBound = Math.min(pb.head.control.settingOptimization.upperBound, ctr != null ? ctr.maxComputableObjectiveValue() : Long.MAX_VALUE);
	}

	/**
	 * Returns the value of the objective, for the current complete instantiation.
	 */
	public final long value() {
		assert Variable.areAllFixed(pb.variables);
		if (ctr != null)
			return ctr.objectiveValue();
		else if (pb.solver.propagation instanceof LowerBoundCapability)
			return ((LowerBoundCapability) pb.solver.propagation).getLowerBound();
		else
			return ((SolverLocal) pb.solver).nMinViolatedCtrs;
	}

	public final boolean isBetterBound(long bound) {
		return minimization ? bound <= maxBound : bound >= minBound;
	}

	protected abstract void shiftLimitWhenSuccess();

	protected abstract void shiftLimitWhenFailure();

	public void afterRun() {
		Kit.control(pb.head.control.settingGeneral.framework == TypeFramework.COP);
		if (pb.solver.solManager.lastSolutionRun == pb.solver.restarter.numRun) { // a better solution has been found during the last run
			if (minimization)
				maxBound = pb.solver.solManager.bestBound - 1;
			else
				minBound = pb.solver.solManager.bestBound + 1;
			possiblyUpdateLocalBounds();
			Kit.control(minBound - 1 <= maxBound || pb.head.control.settingOptimization.upperBound != Long.MAX_VALUE, () -> " minB=" + minBound + " maxB=" + maxBound);
			possiblyUpdateSharedBounds();
			if (minBound > maxBound)
				pb.solver.stopping = EStopping.FULL_EXPLORATION;
			else
				shiftLimitWhenSuccess();
		} else if (pb.solver.stopping == EStopping.FULL_EXPLORATION) { // last run leads to no new solution
			long limit = ctr.getLimit();
			if (minimization)
				minBound = limit == Long.MAX_VALUE ? Long.MAX_VALUE : limit + 1;
			else
				maxBound = limit == Long.MIN_VALUE ? Long.MIN_VALUE : limit - 1;
			Kit.log.fine("\n" + Output.COMMENT_PREFIX + "New Bounds: " + stringBounds());
			if (minBound <= maxBound) {
				pb.solver.stopping = null;
				Kit.control(pb.stuff.nValuesRemovedAtConstructionTime == 0, () -> "Not handled for the moment");
				pb.solver.restarter.forceRootPropagation = true;
				((SolverBacktrack) pb.solver).restoreProblem();
				shiftLimitWhenFailure();
			}
			if (((SolverBacktrack) pb.solver).learnerNogoods != null)
				((SolverBacktrack) pb.solver).learnerNogoods.reset();
		}
	}

	public void shiftLimit(long offset) {
		Kit.control(0 <= offset && minBound + offset <= maxBound, () -> "offset " + offset + " minBound " + minBound + " maxBound " + maxBound);
		long newLimit = minimization ? maxBound - offset : minBound + offset;
		Kit.log.finer(Output.COMMENT_PREFIX + "New Limit: " + newLimit + "\n");
		ctr.setLimit(newLimit);
	}

	public boolean areBoundsConsistent() {
		return minBound <= maxBound;
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
	// SVal not correctly updated in STR2
	// Increasing and Dichotomic to be totally revised

	public static final class OptimizerBasic extends Optimizer {

		public final String optimizationExpression;

		public OptimizerBasic(Problem pb, String optimizationExpression) {
			super(pb, TypeOptimization.MINIMIZE, null);
			this.optimizationExpression = optimizationExpression;
		}

		@Override
		protected void shiftLimitWhenSuccess() {
		}

		@Override
		protected void shiftLimitWhenFailure() {
		}

		@Override
		public String toString() {
			return (minimization ? TypeOptimization.MINIMIZE : TypeOptimization.MAXIMIZE).shortName() + " " + optimizationExpression;
		}
	}

	public static final class OptimizerDecreasing extends Optimizer {

		public OptimizerDecreasing(Problem pb, TypeOptimization opt, Optimizable ctr) {
			super(pb, opt, ctr);
		}

		@Override
		protected void shiftLimitWhenSuccess() {
			shiftLimit(0);
		}

		@Override
		protected void shiftLimitWhenFailure() {
			// throw new UnreachableCodeException();
		}
	}

	public static final class OptimizerIncreasing extends Optimizer {

		boolean first = true;

		public OptimizerIncreasing(Problem pb, TypeOptimization opt, Optimizable ctr) {
			super(pb, opt, ctr);

		}

		@Override
		protected void shiftLimitWhenSuccess() {
			if (first) {
				ctr.setLimit(minimization ? minBound : maxBound);
				Kit.log.info("limit=" + ctr.getLimit());
				first = false;
			} else
				throw new AssertionError();
		}

		@Override
		protected void shiftLimitWhenFailure() {
			ctr.setLimit(minimization ? minBound : maxBound);
		}
	}

	public static final class OptimizerDichotomic extends Optimizer {

		public OptimizerDichotomic(Problem pb, TypeOptimization opt, Optimizable ctr) {
			super(pb, opt, ctr);
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

}
