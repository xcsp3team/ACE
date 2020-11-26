package optimization;

import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Types.TypeOptimization;

import dashboard.Arguments;
import dashboard.Output;
import problem.Problem;
import solver.backtrack.SolverBacktrack;
import solver.local.SolverLocal;
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

	public final Optimizable ctr;

	/**
	 * Solutions searched for must have a cost greater than or equal to this bound (valid for minimization and maximization).
	 */
	public long minBound;

	/**
	 * Solutions searched for must have a cost less than or equal to this bound (valid for minimization and maximization).
	 */
	public long maxBound;

	public Optimizer(Problem pb, TypeOptimization opt, Optimizable c) {
		this.problem = pb;
		Kit.control(opt != null);
		this.minimization = opt == TypeOptimization.MINIMIZE;
		this.ctr = c; // may be null for some basic cases
		this.minBound = Math.max(pb.head.control.optimization.lb, c != null ? c.minComputableObjectiveValue() : Long.MIN_VALUE);
		this.maxBound = Math.min(pb.head.control.optimization.ub, c != null ? c.maxComputableObjectiveValue() : Long.MAX_VALUE);
	}

	/**
	 * Returns the value of the objective, for the current complete instantiation.
	 */
	public final long value() {
		assert Variable.areAllFixed(problem.variables);
		if (ctr != null)
			return ctr.objectiveValue();
		else if (problem.solver.propagation instanceof LowerBoundCapability)
			return ((LowerBoundCapability) problem.solver.propagation).getLowerBound();
		else
			return ((SolverLocal) problem.solver).nMinViolatedCtrs;
	}

	public final boolean isBetterBound(long bound) {
		return minimization ? bound <= maxBound : bound >= minBound;
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
			Kit.control(minBound - 1 <= maxBound || problem.head.control.optimization.ub != Long.MAX_VALUE,
					() -> " minB=" + minBound + " maxB=" + maxBound);
			possiblyUpdateSharedBounds();
			if (minBound > maxBound)
				problem.solver.stopping = EStopping.FULL_EXPLORATION;
			else
				shiftLimitWhenSuccess();
		} else if (problem.solver.stopping == EStopping.FULL_EXPLORATION) { // last run leads to no new solution
			if (minimization)
				minBound = ctr.limit() + 1;
			else
				maxBound = ctr.limit() - 1;
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

	public void shiftLimit(long offset) {
		Kit.control(0 <= offset && minBound + offset <= maxBound, () -> "offset " + offset + " minBound " + minBound + " maxBound " + maxBound);
		long newLimit = minimization ? maxBound - offset : minBound + offset;
		Kit.log.finer(Output.COMMENT_PREFIX + "New Limit: " + newLimit + "\n");
		ctr.limit(newLimit);
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
			if (first) { // we now attempt to find optimality by increasingly updating the bounds (if minimization)
				ctr.limit(minimization ? minBound : maxBound);
				Kit.log.info("limit=" + ctr.limit());
				first = false;
			} else
				throw new AssertionError();
		}

		@Override
		protected void shiftLimitWhenFailure() {
			ctr.limit(minimization ? minBound : maxBound);
		}
	}

	// java ace /home/lecoutre/instances/XCSP18v2/allInstances/Fapp/Fapp-m2s/Fapp-m2s-01-0200_c18.xml.lzma -os=dichotomic -positive=str2 PROBLEM
	// but STR1 ok
	// if decremental set to false in STRoptimized, STR2 ok (but not CT that need decremental); why?
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
