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
import problem.Problem;
import sets.SetDense;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This root class is used when the objective of the problem (constraint network) is given by an expression (involving a single variable) whose value must be
 * minimized or maximized.
 *
 * @author Christophe Lecoutre
 *
 */
public abstract class ObjectiveUnaryExpression extends ConstraintGlobal implements Optimizable, TagAC, TagCallCompleteFiltering, TagNotSymmetric {

	@Override
	public long limit() {
		return limit;
	}

	@Override
	public final void setLimit(long newLimit) {
		this.limit = newLimit;
	}

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

	/**
	 * The variable to be optimized (minimized or maximized)
	 */
	public final Variable x;

	protected final Domain domx;

	/**
	 * The current limit used for optimization
	 */
	protected long limit;

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
	public ObjectiveUnaryExpression(Problem pb, XNode<IVar> tree, long limit) {
		super(pb, new Variable[] { (Variable) tree.var(0) });
		IVar[] vars = tree.vars();
		Kit.control(vars.length == 1);
		this.tree = tree;
		this.x = (Variable) vars[0];
		this.domx = x.dom;
		TreeEvaluator evaluator = new TreeEvaluator(tree);
		this.vals = IntStream.range(0, domx.initSize()).map(a -> Utilities.safeInt(evaluator.evaluate(new int[] { domx.toVal(a) }))).toArray();
		this.setDense = new SetDense(domx.initSize());

		limit(this instanceof ObjExpr1LE ? Math.min(limit, maxComputableObjectiveValue()) : Math.max(limit, minComputableObjectiveValue()));
	}

	/**
	 * The class for an objective unary expression that must be minimized. To enforce convergence, the limit is updated at each new solution and the constraint
	 * enforces that the value of the expression is less than or equal to the current limit.
	 */
	public static final class ObjExpr1LE extends ObjectiveUnaryExpression {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return vals[domx.toIdx(t[0])] <= limit;
		}

		public ObjExpr1LE(Problem pb, XNode<IVar> tree, long limit) {
			super(pb, tree, limit);
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
	 * The class for an objective unary expression that must be maximized. To enforce convergence, the limit is updated at each new solution and the constraint
	 * enforces that the value of the expression is greater than or equal to the current limit.
	 */
	public static final class ObjExpr1GE extends ObjectiveUnaryExpression {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return vals[domx.toIdx(t[0])] >= limit;
		}

		public ObjExpr1GE(Problem pb, XNode<IVar> tree, long limit) {
			super(pb, tree, limit);
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
