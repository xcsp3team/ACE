/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.intension;

import static org.xcsp.common.Types.TypeConditionOperatorRel.EQ;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.NE;
import static org.xcsp.common.Types.TypeConditionOperatorSet.IN;
import static org.xcsp.common.Utilities.safeInt;
import static problem.Problem.k_relop_x;
import static problem.Problem.x_relop_k;
import static problem.Problem.x_setop_vals;
import static utility.Kit.control;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeConditionOperatorSet;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.predicates.XNode;
import org.xcsp.common.predicates.XNodeLeaf;

import constraints.ConstraintGlobal;
import constraints.intension.Logic.LogicTree.ArgLogic.ArgSet.ArgIn;
import constraints.intension.Logic.LogicTree.ArgLogic.ArgSet.ArgNotIn;
import constraints.intension.Logic.LogicTree.ArgLogic.ArgVar;
import constraints.intension.Logic.LogicTree.ArgLogic.ArgdRel.ArgEQ;
import constraints.intension.Logic.LogicTree.ArgLogic.ArgdRel.ArgGE;
import constraints.intension.Logic.LogicTree.ArgLogic.ArgdRel.ArgLE;
import constraints.intension.Logic.LogicTree.ArgLogic.ArgdRel.ArgNE;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotSymmetric;
import problem.Problem;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public abstract class Logic extends ConstraintGlobal implements TagAC, TagCallCompleteFiltering {

	public Logic(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	/**
	 * This constraint ensures that a predicate expression corresponding to a disjunction where each disjunct only involves a (separate) variable is satisfied.
	 * 
	 * @author Christophe Lecoutre
	 */
	public static class LogicTree extends Logic implements TagNotSymmetric { // for identifying symmetry, we should compare disjuncts

		@Override
		public final boolean isSatisfiedBy(int[] t) {
			for (int i = 0; i < logicArgs.length; i++)
				if (logicArgs[i].canBeSatisfiedBy(t[i]))
					return true;
			return false;
		}

		final XNode<IVar>[] trees;

		final ArgLogic[] logicArgs;

		ArgLogic sentinel1, sentinel2;

		private ArgLogic[] buildLogicArgs(XNode<IVar>[] trees) {
			List<ArgLogic> list = new ArrayList<>();

			for (XNode<IVar> tree : trees) {
				Domain dom = ((Variable) tree.var(0)).dom; // remember that the tree only involves a single variable
				if (tree.type == TypeExpr.VAR)
					list.add(new ArgVar(dom));
				else if (x_relop_k.matches(tree)) {
					TypeConditionOperatorRel op = tree.relop(0);
					int k = tree.val(0);
					control(op.oneOf(LE, GE, NE, EQ)); // because the tree is in canonical form
					list.add(op == LE ? new ArgLE(dom, k) : op == GE ? new ArgGE(dom, k) : op == NE ? new ArgNE(dom, k) : new ArgEQ(dom, k));
				} else if (k_relop_x.matches(tree)) {
					TypeConditionOperatorRel op = tree.relop(0);
					int k = tree.val(0);
					control(op.oneOf(LE, GE, NE, EQ)); // because the tree is in canonical form
					list.add(op == LE ? new ArgGE(dom, k) : op == GE ? new ArgLE(dom, k) : op == NE ? new ArgNE(dom, k) : new ArgEQ(dom, k));
				} else {
					control(x_setop_vals.matches(tree), " " + tree);
					TypeConditionOperatorSet op = tree.setop(0);
					int[] vals = Stream.of(tree.sons[1].sons).mapToInt(s -> safeInt((long) ((XNodeLeaf<?>) s).value)).toArray();
					list.add(op == IN ? new ArgIn(dom, vals) : new ArgNotIn(dom, vals));
				}
			}
			// System.out.println("aaaa" + Kit.join(trees) + " " + Kit.join(list.stream().map(ll -> ll.getClass().getSimpleName())));
			return list.toArray(ArgLogic[]::new);
		}

		public LogicTree(Problem pb, XNode<IVar>[] trees) {
			super(pb, Stream.of(trees).map(tree -> tree.var(0)).toArray(Variable[]::new));
			control(trees.length > 1 && Stream.of(trees).allMatch(tree -> tree.vars().length == 1));
			assert scp.length == trees.length && IntStream.range(0, scp.length).allMatch(i -> scp[i] == trees[i].var(0)) : " " + Kit.join(trees);

			this.trees = trees;
			this.logicArgs = buildLogicArgs(trees);
			this.sentinel1 = logicArgs[0];
			this.sentinel2 = logicArgs[logicArgs.length - 1];
		}

		private ArgLogic findSentinel(ArgLogic other) {
			for (ArgLogic logicArg : logicArgs)
				if (logicArg != other && logicArg.canBe1())
					return logicArg;
			return null;
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (!sentinel1.canBe1()) {
				ArgLogic sent = findSentinel(sentinel2);
				if (sent == null)
					return sentinel2.enforce1() && entail();
				sentinel1 = sent;
			}
			if (!sentinel1.canBe0())
				return entail();
			if (!sentinel2.canBe1()) {
				ArgLogic sent = findSentinel(sentinel1);
				if (sent == null)
					return sentinel1.enforce1() && entail();
				sentinel2 = sent;
			}
			if (!sentinel2.canBe0())
				return entail();
			return true;
		}

		/**********************************************************************************************
		 * Classes for unary conditions/arguments, i.e., 0/1 tree expressions involving only one variable
		 *********************************************************************************************/

		static interface ArgLogic {

			boolean canBeSatisfiedBy(int v);

			boolean canBe1();

			boolean canBe0();

			boolean enforce1();

			static abstract class ArgdRel implements ArgLogic {
				protected Domain dom;
				protected int k;

				ArgdRel(Domain dom, int k) {
					this.dom = dom;
					this.k = k;
				}

				static class ArgLE extends ArgdRel {

					ArgLE(Domain dom, int k) {
						super(dom, k);
					}

					public boolean canBeSatisfiedBy(int v) {
						return v <= k;
					}

					public boolean canBe0() {
						return dom.lastValue() > k;
					}

					public boolean canBe1() {
						return dom.firstValue() <= k;
					}

					public boolean enforce1() {
						return dom.removeValuesGT(k);
					}
				}

				static class ArgGE extends ArgdRel {

					ArgGE(Domain dom, int k) {
						super(dom, k);
					}

					public boolean canBeSatisfiedBy(int v) {
						return v >= k;
					}

					public boolean canBe0() {
						return dom.firstValue() < k;
					}

					public boolean canBe1() {
						return dom.lastValue() >= k;
					}

					public boolean enforce1() {
						return dom.removeValuesLT(k);
					}
				}

				static class ArgEQ extends ArgdRel {

					ArgEQ(Domain dom, int k) {
						super(dom, k);
					}

					public boolean canBeSatisfiedBy(int v) {
						return v == k;
					}

					public boolean canBe0() {
						return dom.size() > 1 || dom.singleValue() != k;
					}

					public boolean canBe1() {
						return dom.containsValue(k);
					}

					public boolean enforce1() {
						return dom.reduceToValue(k);
					}
				}

				static class ArgNE extends ArgdRel {

					ArgNE(Domain dom, int k) {
						super(dom, k);
					}

					public boolean canBeSatisfiedBy(int v) {
						return v != k;
					}

					public boolean canBe0() {
						return dom.containsValue(k);
					}

					public boolean canBe1() {
						return dom.size() > 1 || dom.singleValue() != k;
					}

					public boolean enforce1() {
						return dom.removeValueIfPresent(k);
					}
				}
			}

			static abstract class ArgSet implements ArgLogic {
				protected Domain dom;
				protected int[] vals;

				protected int sentinel0, sentinel1;

				protected int findIndexOfPresentValue() {
					int i = 0;
					for (int a = dom.first(); a != -1; a = dom.next(a)) {
						int v = dom.toVal(a);
						while (i < vals.length && vals[i] < v)
							i++;
						if (i == vals.length)
							return -1;
						if (vals[i] == v)
							return a;
					}
					return -1;
				}

				protected int findIndexOfNotPresentValue() {
					int i = 0;
					for (int a = dom.first(); a != -1; a = dom.next(a)) {
						int v = dom.toVal(a);
						while (i < vals.length && vals[i] < v)
							i++;
						if (i == vals.length || vals[i] > v)
							return a;
					}
					return -1;
				}

				ArgSet(Domain dom, int[] vals) {
					this.dom = dom;
					this.vals = vals;
					control(vals.length > 1 && dom.size() > vals.length && IntStream.of(vals).allMatch(v -> dom.containsValue(v))
							&& IntStream.range(0, vals.length - 1).allMatch(i -> vals[i] < vals[i + 1]));
				}

				static class ArgIn extends ArgSet {

					ArgIn(Domain dom, int[] vals) {
						super(dom, vals);
						this.sentinel0 = findIndexOfNotPresentValue();
						this.sentinel1 = findIndexOfPresentValue();
						control(sentinel0 != -1 && sentinel1 != -1, " " + dom + " " + Kit.join(vals));
					}

					public boolean canBeSatisfiedBy(int v) {
						int i = 0;
						while (i < vals.length && vals[i] < v)
							i++;
						return i < vals.length && vals[i] == v;
					}

					public boolean canBe0() {
						if (dom.contains(sentinel0))
							return true;
						int sent = findIndexOfNotPresentValue();
						if (sent == -1)
							return false;
						sentinel0 = sent;
						return true;
					}

					public boolean canBe1() {
						if (dom.contains(sentinel1))
							return true;
						int sent = findIndexOfPresentValue();
						if (sent == -1)
							return false;
						sentinel1 = sent;
						return true;
					}

					public boolean enforce1() {
						return dom.removeValuesNotIn(vals);
					}
				}

				static class ArgNotIn extends ArgSet {

					ArgNotIn(Domain dom, int[] vals) {
						super(dom, vals);
						this.sentinel0 = findIndexOfPresentValue();
						this.sentinel1 = findIndexOfNotPresentValue();
						control(sentinel0 != -1 && sentinel1 != -1);
					}

					public boolean canBeSatisfiedBy(int v) {
						int i = 0;
						while (i < vals.length && vals[i] < v)
							i++;
						return i == vals.length || vals[i] > v;
					}

					public boolean canBe0() {
						if (dom.contains(sentinel0))
							return true;
						int sent = findIndexOfPresentValue();
						if (sent == -1)
							return false;
						sentinel0 = sent;
						return true;
					}

					public boolean canBe1() {
						if (dom.contains(sentinel1))
							return true;
						int sent = findIndexOfNotPresentValue();
						if (sent == -1)
							return false;
						sentinel1 = sent;
						return true;
					}

					public boolean enforce1() {
						return dom.removeValuesIn(vals);
					}
				}
			}

			static class ArgVar implements ArgLogic {
				protected Domain dom;

				ArgVar(Domain dom) {
					this.dom = dom;
					control(dom.is01());
				}

				public boolean canBeSatisfiedBy(int v) {
					return v == 1;
				}

				public boolean canBe0() {
					return dom.first() == 0;
				}

				public boolean canBe1() {
					return dom.last() == 1;
				}

				public boolean enforce1() {
					return dom.removeIfPresent(0);
				}
			}
		}
	}
}

// LogicVarAnd => not relevant as we can post separate constraints
// LogicVarOr => not relevant as we can post Sum(xi) >= 1
