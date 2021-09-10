package optimization;

import static utility.Kit.control;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import variables.Variable;

public abstract class ObjectiveVariable extends ConstraintGlobal implements Optimizable, TagAC, TagCallCompleteFiltering, TagSymmetric {

	@Override
	public long minComputableObjectiveValue() {
		return x.dom.toVal(0);
	}

	@Override
	public long maxComputableObjectiveValue() {
		return x.dom.toVal(x.dom.initSize() - 1);
	}

	@Override
	public long minCurrentObjectiveValue() {
		return x.dom.firstValue();
	}

	@Override
	public long maxCurrentObjectiveValue() {
		return x.dom.lastValue();
	}

	@Override
	public long limit() {
		return limit;
	}

	@Override
	public final void limit(long newLimit) {
		this.limit = newLimit;
		control(minComputableObjectiveValue() - 1 <= limit && limit <= maxComputableObjectiveValue() + 1);
	}

	@Override
	public long objectiveValue() {
		return x.dom.singleValue();
	}

	/**
	 * The variable to be optimized (minimized or maximized)
	 */
	protected Variable x;

	/**
	 * The current limit used for optimization
	 */
	protected long limit;

	/**
	 * Builds an objective for the specified problem represented by the specified variable, with initially the specified limit
	 * 
	 * @param pb
	 *            the problem to which the objective is attached
	 * @param x
	 *            the variable representing the objective
	 * @param limit
	 *            the initial limit for the objective constraint
	 */
	public ObjectiveVariable(Problem pb, Variable x, long limit) {
		super(pb, new Variable[] { x });
		this.x = x;
		limit(limit);
	}

	/**
	 * The class for an objective variable that must be minimized. To enforce convergence, the limit is updated at each new solution and the constraint enforces
	 * that the value of the variable is less than or equal to the current limit.
	 */
	public static final class ObjVarLE extends ObjectiveVariable {

		@Override
		public boolean isSatisfiedBy(int[] vals) {
			return vals[0] <= limit;
		}

		public ObjVarLE(Problem pb, Variable x, long limit) {
			super(pb, x, Math.min(limit, x.dom.lastValue()));
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			control(problem.solver.depth() == 0, () -> "depth: " + problem.solver.depth());
			if (x.dom.removeValuesGT(limit) == false)
				return false;
			assert x.dom.size() > 0;
			return entailed();
		}
	}

	public static final class ObjVarGE extends ObjectiveVariable {

		@Override
		public boolean isSatisfiedBy(int[] vals) {
			return vals[0] >= limit;
		}

		public ObjVarGE(Problem pb, Variable x, long limit) {
			super(pb, x, Math.max(limit, x.dom.firstValue()));
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			control(problem.solver.depth() == 0, () -> "depth: " + problem.solver.depth());
			if (x.dom.removeValuesLT(limit) == false)
				return false;
			assert x.dom.size() > 0;
			return entailed();
		}
	}
}
