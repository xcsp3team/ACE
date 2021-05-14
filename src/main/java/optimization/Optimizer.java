package optimization;

import static org.xcsp.common.Types.TypeFramework.COP;
import static org.xcsp.common.Types.TypeOptimization.MAXIMIZE;
import static org.xcsp.common.Types.TypeOptimization.MINIMIZE;
import static utility.Enums.EStopping.FULL_EXPLORATION;

import org.xcsp.common.Types.TypeOptimization;

import dashboard.Input;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public abstract class Optimizer { // Pilot for (mono-objective) optimization

	/**********************************************************************************************
	 * Sharing bounds between workers
	 *********************************************************************************************/

	private static Long sharedMinBound = Long.MIN_VALUE;
	private static Long sharedMaxBound = Long.MAX_VALUE;

	public final boolean possiblyUpdateSharedBounds() {
		if (!Input.multiThreads)
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
		if (!Input.multiThreads)
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
		this.minimization = opt == MINIMIZE;
		this.clb = clb;
		this.cub = cub;
		this.ctr = opt == MINIMIZE ? cub : clb; // the leading constraint (used at some places in other classes)
		this.minBound = clb.limit();
		this.maxBound = cub.limit();
	}

	/**
	 * Returns the value of the objective, for the current complete instantiation.
	 */
	public final long value() {
		assert Variable.areAllFixed(problem.variables) && clb.objectiveValue() == cub.objectiveValue();
		return cub.objectiveValue();
	}

	protected abstract void shiftLimitWhenSuccess();

	protected abstract void shiftLimitWhenFailure();

	public void afterRun() {
		Kit.control(problem.head.control.general.framework == COP);
		if (problem.solver.solRecorder.lastSolutionRun == problem.solver.restarter.numRun) { // a better solution has been found during the last run
			if (minimization) {
				maxBound = problem.solver.solRecorder.bestBound - 1;
				cub.limit(maxBound);
			} else {
				minBound = problem.solver.solRecorder.bestBound + 1;
				clb.limit(minBound);
			}
			possiblyUpdateLocalBounds();
			Kit.control(minBound - 1 <= maxBound || problem.head.control.optimization.ub != Long.MAX_VALUE, () -> " minB=" + minBound + " maxB=" + maxBound);
			possiblyUpdateSharedBounds();
			if (minBound > maxBound)
				problem.solver.stopping = FULL_EXPLORATION;
			else
				shiftLimitWhenSuccess();
		} else if (problem.solver.stopping == FULL_EXPLORATION) { // last run leads to no new solution
			boolean clb_changed = clb.limit() != minBound, cub_changed = cub.limit() != maxBound;
			Kit.control(!clb_changed || !cub_changed);
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
				Kit.control(problem.features.nValuesRemovedAtConstructionTime == 0, () -> "Not handled for the moment");
				problem.solver.restarter.forceRootPropagation = true;
				problem.solver.restoreProblem();
				if (problem.solver.nogoodRecorder != null)
					problem.solver.nogoodRecorder.reset();
				shiftLimitWhenFailure();
			}
		}
	}

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

	// TODO problem when incremental is used with STR2 and CT for Increasing and Dichotomic
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
			// nothing to do
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

	// java ace /home/lecoutre/instances/XCSP18v2/allInstances/Fapp/Fapp-m2s/Fapp-m2s-01-0200_c18.xml.lzma -os=dichotomic -positive=str2 PROBLEM
	// but STR1 ok
	// If decremental set to false in STRoptimized, STR2 ok (but not CT that need decremental); why? // TODO
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
}
