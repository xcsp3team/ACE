/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package optimization;

import java.util.stream.IntStream;

import org.xcsp.common.IVar;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.TreeEvaluator;
import org.xcsp.common.predicates.XNode;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotSymmetric;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import sets.SetDense;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This root class is used when the objective of the problem (constraint network) is given by a unary expression, i.e., either a variable or a tree expression
 * involving a single variable.
 *
 * @author Christophe Lecoutre
 *
 */
public abstract class ObjectiveUnary extends ConstraintGlobal implements Optimizable, TagAC, TagCallCompleteFiltering {

	/**
	 * The involved variable
	 */
	public final Variable x;

	protected final Domain domx;

	/**
	 * The current limit used for optimization
	 */
	protected long limit;

	@Override
	public final long limit() {
		return limit;
	}

	@Override
	public final void setLimit(long newLimit) {
		this.limit = newLimit;
	}

	public ObjectiveUnary(Problem pb, Variable x) {
		super(pb, new Variable[] { x });
		this.x = x;
		this.domx = x.dom;
	}

	/**
	 * This root class is used when the objective of the problem (constraint network) is given by an expression (involving a single variable) whose value must
	 * be minimized or maximized.
	 *
	 * @author Christophe Lecoutre
	 *
	 */
	public abstract static class ObjectiveExpression extends ObjectiveUnary implements TagNotSymmetric {

		@Override
		public long minComputableObjectiveValue() {
			return IntStream.of(vals).min().getAsInt();
		}

		@Override
		public long maxComputableObjectiveValue() {
			return IntStream.of(vals).max().getAsInt();
		}

		@Override
		public long minCurrentObjectiveValue() {
			int vmin = Integer.MAX_VALUE;
			for (int a = domx.first(); a != -1; a = domx.next(a))
				vmin = Math.min(vmin, vals[a]);
			return vmin;
		}

		@Override
		public long maxCurrentObjectiveValue() {
			int vmax = Integer.MIN_VALUE;
			for (int a = domx.first(); a != -1; a = domx.next(a))
				vmax = Math.max(vmax, vals[a]);
			return vmax;
		}

		@Override
		public long objectiveValue() {
			return vals[domx.single()];
		}

		public final XNode<IVar> tree;

		protected final int[] vals;

		protected final SetDense setDense;

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
		public ObjectiveExpression(Problem pb, XNode<IVar> tree) {
			super(pb, (Variable) tree.var(0));
			Kit.control(tree.vars().length == 1);
			this.tree = tree;
			TreeEvaluator evaluator = new TreeEvaluator(tree);
			this.vals = IntStream.range(0, domx.initSize()).map(a -> Utilities.safeInt(evaluator.evaluate(new int[] { domx.toVal(a) }))).toArray();
			this.setDense = new SetDense(domx.initSize());
		}

		/**
		 * The class for an objective unary expression that must be minimized. To enforce convergence, the limit is updated at each new solution and the
		 * constraint enforces that the value of the expression is less than or equal to the current limit.
		 */
		public static final class ObjExpr1LE extends ObjectiveExpression {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return vals[domx.toIdx(t[0])] <= limit;
			}

			public ObjExpr1LE(Problem pb, XNode<IVar> tree, long limit) {
				super(pb, tree);
				limit(Math.min(limit, maxComputableObjectiveValue()));
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// control(problem.solver.depth() == 0, () -> "depth: " + problem.solver.depth());
				setDense.clear();
				for (int a = domx.first(); a != -1; a = domx.next(a))
					if (vals[a] > limit)
						setDense.add(a);
				if (domx.remove(setDense) == false)
					return false;
				assert x.dom.size() > 0;
				return entail();
			}
		}

		/**
		 * The class for an objective unary expression that must be maximized. To enforce convergence, the limit is updated at each new solution and the
		 * constraint enforces that the value of the expression is greater than or equal to the current limit.
		 */
		public static final class ObjExpr1GE extends ObjectiveExpression {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return vals[domx.toIdx(t[0])] >= limit;
			}

			public ObjExpr1GE(Problem pb, XNode<IVar> tree, long limit) {
				super(pb, tree);
				limit(Math.max(limit, minComputableObjectiveValue()));
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// control(problem.solver.depth() == 0, () -> "depth: " + problem.solver.depth());
				setDense.clear();
				for (int a = domx.first(); a != -1; a = domx.next(a))
					if (vals[a] < limit)
						setDense.add(a);
				if (domx.remove(setDense) == false)
					return false;
				assert x.dom.size() > 0;
				return entail();
			}
		}
	}

	/**
	 * This root class is used when the objective of the problem (constraint network) is given by a variable whose value must be minimized or maximized.
	 *
	 * @author Christophe Lecoutre
	 *
	 */
	public abstract static class ObjectiveVariable extends ObjectiveUnary implements TagSymmetric {

		@Override
		public long minComputableObjectiveValue() {
			return domx.smallestInitialValue();
		}

		@Override
		public long maxComputableObjectiveValue() {
			return domx.greatestInitialValue();
		}

		@Override
		public long minCurrentObjectiveValue() {
			return domx.firstValue();
		}

		@Override
		public long maxCurrentObjectiveValue() {
			return domx.lastValue();
		}

		@Override
		public long objectiveValue() {
			return domx.singleValue();
		}

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
			super(pb, x);
			limit(limit);
		}

		/**
		 * The class for an objective variable that must be minimized. To enforce convergence, the limit is updated at each new solution and the constraint
		 * enforces that the value of the variable is less than or equal to the current limit.
		 */
		public static final class ObjVarLE extends ObjectiveVariable {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] <= limit;
			}

			public ObjVarLE(Problem pb, Variable x, long limit) {
				super(pb, x, Math.min(limit, x.dom.lastValue()));
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// control(problem.solver.depth() == 0, () -> "depth: " + problem.solver.depth());
				if (domx.removeValuesGT(limit) == false)
					return false;
				assert domx.size() > 0;
				return entail();
			}
		}

		/**
		 * The class for an objective variable that must be maximized. To enforce convergence, the limit is updated at each new solution and the constraint
		 * enforces that the value of the variable is greater than or equal to the current limit.
		 */
		public static final class ObjVarGE extends ObjectiveVariable {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] >= limit;
			}

			public ObjVarGE(Problem pb, Variable x, long limit) {
				super(pb, x, Math.max(limit, x.dom.firstValue()));
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// control(problem.solver.depth() == 0, () -> "depth: " + problem.solver.depth());
				if (domx.removeValuesLT(limit) == false)
					return false;
				assert domx.size() > 0;
				return entail();
			}
		}
	}

}
