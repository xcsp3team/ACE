/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import static org.xcsp.common.predicates.MatcherInterface.k_le_x;
import static org.xcsp.common.predicates.MatcherInterface.x_eq_k;
import static org.xcsp.common.predicates.MatcherInterface.x_ge_k;
import static org.xcsp.common.predicates.MatcherInterface.x_gt_k;
import static org.xcsp.common.predicates.MatcherInterface.x_le_k;
import static org.xcsp.common.predicates.MatcherInterface.x_lt_k;
import static org.xcsp.common.predicates.MatcherInterface.x_ne_k;
import static utility.Kit.control;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import org.xcsp.common.IVar;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.predicates.XNode;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * This constraint ensures that at least one of the terms of the 'clause' is true. Each term is a tree expression involving a single variable.
 * 
 * @author Christophe Lecoutre
 */
public class ClauseUnaryTrees extends ConstraintGlobal implements TagAC, TagCallCompleteFiltering {

	public static TreeUnaryBoolean[] canBuildTreeUnaryBooleans(XNode<IVar>[] trees) {
		assert Stream.of(trees).allMatch(tree -> tree.vars().length == 1);
		List<TreeUnaryBoolean> list = new ArrayList<>();
		for (XNode<?> tree : trees) {
			Variable x = (Variable) tree.var(0);
			if (tree.type == TypeExpr.VAR && x.dom.is01())
				list.add(new TreeUnaryBoolean.TreeVAR(x));
			else {
				if (!tree.type.isRelationalOperator()) // TODO and IN, NOTIN
					return null;
				if (x_eq_k.matches(tree))
					list.add(new TreeUnaryBoolean.TreeEQ(x, tree.val(0)));
				else if (x_ne_k.matches(tree))
					list.add(new TreeUnaryBoolean.TreeNE(x, tree.val(0)));
				else if (x_lt_k.matches(tree))
					list.add(new TreeUnaryBoolean.TreeLE(x, tree.val(0) - 1));
				else if (x_le_k.matches(tree))
					list.add(new TreeUnaryBoolean.TreeLE(x, tree.val(0)));
				else if (k_le_x.matches(tree))
					list.add(new TreeUnaryBoolean.TreeGE(x, tree.val(0)));
				else if (x_ge_k.matches(tree))
					list.add(new TreeUnaryBoolean.TreeGE(x, tree.val(0)));
				else if (x_gt_k.matches(tree))
					list.add(new TreeUnaryBoolean.TreeGE(x, tree.val(0) + 1));
				else 
					return null;
			}
		}
		return list.toArray(TreeUnaryBoolean[]::new);
	}

	public static abstract class TreeUnaryBoolean {
		protected Variable x;

		protected Domain dx;

		public TreeUnaryBoolean(Variable x) {
			this.x = x;
			this.dx = x.dom;
		}

		public abstract boolean canFindFalse();

		public abstract boolean canFindTrue();

		public abstract boolean enforceTrue();

		public abstract boolean check(int v);

		public static class TreeEQ extends TreeUnaryBoolean {

			private int k;

			public TreeEQ(Variable x, int k) {
				super(x);
				this.k = k;
			}

			public boolean canFindFalse() {
				return dx.size() > 1 || dx.singleValue() != k;
			}

			public boolean canFindTrue() {
				return dx.containsValue(k);
			}

			public boolean enforceTrue() {
				return dx.reduceTo(k);
			}

			public boolean check(int v) {
				return v == k;
			}

		}

		public static class TreeNE extends TreeUnaryBoolean {

			private int k;

			public TreeNE(Variable x, int k) {
				super(x);
				this.k = k;
			}

			public boolean canFindFalse() {
				return dx.containsValue(k);
			}

			public boolean canFindTrue() {
				return dx.size() > 1 || dx.singleValue() != k;
			}

			public boolean enforceTrue() {
				return dx.removeValue(k);
			}

			public boolean check(int v) {
				return v != k;
			}
		}

		public static class TreeLE extends TreeUnaryBoolean {

			private int k;

			public TreeLE(Variable x, int k) {
				super(x);
				this.k = k;
			}

			public boolean canFindFalse() {
				return dx.lastValue() > k;
			}

			public boolean canFindTrue() {
				return dx.firstValue() <= k;
			}

			public boolean enforceTrue() {
				return dx.removeValuesGT(k);
			}

			public boolean check(int v) {
				return v <= k;
			}
		}

		public static class TreeGE extends TreeUnaryBoolean {

			private int k;

			public TreeGE(Variable x, int k) {
				super(x);
				this.k = k;
			}

			public boolean canFindFalse() {
				return dx.firstValue() < k;
			}

			public boolean canFindTrue() {
				return dx.lastValue() >= k;
			}

			public boolean enforceTrue() {
				return dx.removeValuesLT(k);
			}

			public boolean check(int v) {
				return v >= k;
			}
		}

		public static class TreeVAR extends TreeUnaryBoolean {

			public TreeVAR(Variable x) {
				super(x);
				control(dx.is01());
			}

			public boolean canFindFalse() {
				return dx.first() == 0;
			}

			public boolean canFindTrue() {
				return dx.last() == 1;
			}

			public boolean enforceTrue() {
				return dx.remove(0);
			}

			public boolean check(int v) {
				return v == 1;
			}
		}

		// TODO TreeIn and TreeNOTIN
	}

	private TreeUnaryBoolean[] terms;

	private int sentinel1 = -1, sentinel2 = -1;

	private static final int ENTAILED = -2;

	@Override
	public final boolean isSatisfiedBy(int[] t) {
		for (int i = 0; i < t.length; i++)
			if (terms[i].check(t[i]))
				return true;
		return false;
	}

	public ClauseUnaryTrees(Problem pb, TreeUnaryBoolean[] terms) {
		super(pb, Stream.of(terms).map(term -> term.x).toArray(Variable[]::new));
		control(scp.length >= 2 && scp.length == terms.length);
		this.terms = terms;
	}

	private int findSentinel() {
		for (int i = 0; i < terms.length; i++) {
			if (!terms[i].canFindFalse())
				return ENTAILED;
			if (i != sentinel1 && i != sentinel2 && terms[i].canFindTrue())
				return i;
		}
		return -1;
	}

	@Override
	public boolean runPropagator(Variable event) {
		if (sentinel1 == -1 || !terms[sentinel1].canFindFalse() || !terms[sentinel1].canFindTrue()) {
			int sent = findSentinel();
			if (sent == ENTAILED)
				return entail();
			if (sent == -1) {
				if (sentinel2 == -1)
					return event.dom.fail();
				return terms[sentinel2].enforceTrue() && entail();
			} else
				sentinel1 = sent;
		}
		if (sentinel2 == -1 || !terms[sentinel2].canFindFalse() || !terms[sentinel2].canFindTrue()) {
			int sent = findSentinel();
			if (sent == ENTAILED)
				return entail();
			if (sent == -1) {
				if (sentinel1 == -1)
					return event.dom.fail();
				return terms[sentinel1].enforceTrue() && entail();
			} else
				sentinel2 = sent;
		}
		return true;
	}
}
