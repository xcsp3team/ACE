/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints;

import static utility.Kit.control;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.IVar;
import org.xcsp.common.Types;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.TreeEvaluator;
import org.xcsp.common.predicates.TreeEvaluator.F1Evaluator;
import org.xcsp.common.predicates.TreeEvaluator.F2Evaluator;
import org.xcsp.common.predicates.TreeEvaluator.LongEvaluator;
import org.xcsp.common.predicates.XNodeLeaf;
import org.xcsp.common.predicates.XNodeParent;

import interfaces.ConstraintRegister;
import interfaces.Tags.TagCallCompleteFiltering;
import optimization.Optimizable;
import problem.Problem;
import propagation.Forward;
import propagation.Reviser;
import utility.Kit;
import variables.Variable;
import variables.Variable.VariableInteger;

/**
 * The abstract class representing Intension constraints, which are constraints whose semantics is given by a Boolean expression tree involving variables. Most
 * of the times, primitives are used instead of this general form.
 * 
 * @author Christophe Lecoutre
 */
public final class ConstraintIntension extends Constraint implements TagCallCompleteFiltering, Optimizable {

	public static boolean tooLarge(int size1, int size2, int spaceLimit) {
		return size1 > 1 && size2 > 1 && size1 * (double) size2 > spaceLimit;
	}

	/**********************************************************************************************
	 * Intention structure
	 *********************************************************************************************/

	/**
	 * The structure for managing Boolean expression trees. This is basically a tree evaluator with additional information concerning which constraints share
	 * the same structures.
	 */
	public final static class IntensionStructure extends TreeEvaluator implements ConstraintRegister {

		private final List<Constraint> registeredCtrs = new ArrayList<>();

		@Override
		public List<Constraint> registeredCtrs() {
			return registeredCtrs;
		}

		/**
		 * Builds an intension structure for the specified Boolean expression tree
		 * 
		 * @param tree
		 *            a Boolean expression tree
		 */
		public IntensionStructure(XNodeParent<? extends IVar> tree) {
			super(tree);
		}

		/**
		 * Builds an intension structure for the specified Boolean expression tree, while using the specified map of symbols because symbolic variables are
		 * involved
		 * 
		 * @param tree
		 *            a Boolean expression tree
		 * @param mapOfSymbols
		 *            a map of symbols associating specific integers to symbols (tokens)
		 */
		public IntensionStructure(XNodeParent<? extends IVar> tree, Map<String, Integer> mapOfSymbols) {
			super(tree, mapOfSymbols);
		}
	}

	/**********************************************************************************************
	 * Key Canonizer
	 *********************************************************************************************/

	/**
	 * A class useful to compute canonical forms of intension constraints. This is useful for example for symmetry-breaking.
	 */
	public final static class KeyCanonizer {

		private static final String SUB_ABS = "subabs";

		/**********************************************************************************************
		 * Intern class: Node
		 *********************************************************************************************/

		private final static class Node implements Comparable<Node> {

			@Override
			public int compareTo(Node node) {
				if (sons.length > node.sons.length)
					return -1;
				if (sons.length < node.sons.length)
					return +1;
				if (sons.length == 0) {
					if (label.startsWith("%"))
						return Utilities.isInteger(node.label) ? -1 : label.compareTo(node.label);
					if (node.label.startsWith("%"))
						return +1;
					int i1 = Integer.parseInt(label), i2 = Integer.parseInt(node.label);
					return i1 < i2 ? -1 : i1 == i2 ? 0 : +1;
				}
				if (!label.equals(node.label))
					return label.compareTo(node.label);
				for (int i = 0; i < sons.length; i++) {
					int res = sons[i].compareTo(node.sons[i]);
					if (res != 0)
						return res;
				}
				return 0;
			}

			private String label;

			private Node[] sons;

			private Node(String label, Node... sons) {
				this.label = label;
				this.sons = sons;
			}

			private Node cloneUnderPermutation(String label1, String label2) {
				if (sons.length == 0)
					return label.equals(label1) ? new Node(label2) : label.equals(label2) ? new Node(label1) : new Node(label);
				return new Node(label, Stream.of(sons).map(son -> son.cloneUnderPermutation(label1, label2)).toArray(Node[]::new));
			}

			private void renderCanonical() {
				if (sons.length > 1) {
					for (Node son : sons)
						son.renderCanonical();
					if (label.equals(SUB_ABS) || TreeEvaluator.isSymmetric(label))
						Arrays.sort(sons);
					else if (sons.length == 2) {
						TypeConditionOperatorRel operator = Types.valueOf(TypeConditionOperatorRel.class, label);
						if (operator != null && Utilities.isInteger(sons[0].label) && !Utilities.isInteger(sons[1].label)) {
							label = operator.arithmeticInversion().toString().toLowerCase();
							Kit.swap(sons);
							// TODO : just keep LT and GT by modifying limit (so as to find more equivalent expressions)?
						}
					}
				}
			}

			private StringBuilder toStringBuilder(StringBuilder sb) {
				for (int i = 0; i < sons.length; i++)
					sons[i].toStringBuilder(sb).append(' ');
				return sb.append(label);
			}

			@Override
			public String toString() {
				return toStringBuilder(new StringBuilder()).toString();
			}
		}

		/**********************************************************************************************
		 * Class members
		 *********************************************************************************************/

		/**
		 * The initial tree expression
		 */
		private XNodeParent<IVar> tree;

		/**
		 * The root of the new tree expression that is built in order to get a canonized form
		 */
		private Node root;

		/**
		 * Returns the canonical form of the initially specified tree expression, under the form of a String
		 * 
		 * @return the canonical form of the initially specified tree expression
		 */
		public String key() {
			return root.toString();
		}

		public KeyCanonizer(XNodeParent<IVar> tree) {
			this.tree = tree;
			this.root = buildInitialTree();
			// System.out.println(root);
			root.renderCanonical();
		}

		private Node buildInitialTree() {
			Stack<Node> stack = new Stack<>();
			for (String token : tree.toPostfixExpression(tree.vars()).split(Constants.REG_WS)) {
				int arity = TreeEvaluator.arityOf(token);
				if (arity == 0 || arity == -1)
					stack.push(new Node(token));
				else if (arity == 1) {
					Node son = stack.pop();
					if (token.equals(TypeExpr.ABS.lcname) && son.label.equals(TypeExpr.SUB.lcname)) {
						son.label = SUB_ABS;
						stack.push(son);
					} else
						stack.push(new Node(token, son));
				} else if (arity == 2) {
					Node son2 = stack.pop();
					Node son1 = stack.pop();
					if (TreeEvaluator.isSymmetric(token) && Utilities.isInteger(son1.label) && !Utilities.isInteger(son2.label)) {
						Node tmp = son1;
						son1 = son2;
						son2 = tmp;
					}
					if (TreeEvaluator.isAssociative(token) && (son2.label.equals(token) || son1.label.equals(token))) {
						Node[] sons = new Node[(son2.label.equals(token) ? son2.sons.length : 1) + (son1.label.equals(token) ? son1.sons.length : 1)];
						int cnt = 0;
						if (son2.label.equals(token))
							for (Node son : son2.sons)
								sons[cnt++] = son;
						else
							sons[cnt++] = son2;
						if (son1.label.equals(token))
							for (Node son : son1.sons)
								sons[cnt++] = son;
						else
							sons[cnt++] = son1;
						stack.push(new Node(token, sons));

					} else {
						stack.push(new Node(token, son1, son2));
					}
				} else { // if (arity == 3) {
					Node[] childs = new Node[arity];
					for (int j = arity - 1; j >= 0; j--)
						childs[j] = stack.pop();
					stack.push(new Node(token, childs));
				}
			}
			assert stack.size() == 1;
			return stack.pop();
		}

		public int[] computeSymmetryMatching() {
			int[] permutation = new int[tree.vars().length];
			int color = 1;
			for (int i = 0; i < permutation.length; i++) {
				if (permutation[i] != 0)
					continue;
				for (int j = i + 1; j < permutation.length; j++) {
					if (permutation[j] != 0)
						continue;
					Node node = root.cloneUnderPermutation("%" + i, "%" + j);
					node.renderCanonical();
					if (node.compareTo(root) == 0)
						permutation[j] = color;
				}
				permutation[i] = color++;
			}
			return permutation;
		}
	}

	/**********************************************************************************************
	 * When used for optimization
	 *********************************************************************************************/

	private TreeEvaluator optTreeEvaluator;

	private XNodeLeaf<IVar> node;

	private LongEvaluator le;

	private int[] tmp;

	public void setOptimizationStuff() {
		control((tree.type == TypeExpr.LE || tree.type == TypeExpr.GE) && tree.sons.length == 2 && tree.sons[1].type == TypeExpr.LONG);
		this.optTreeEvaluator = new TreeEvaluator(tree.sons[0]);
		this.node = (XNodeLeaf<IVar>) tree.sons[1];
		this.le = (LongEvaluator) treeEvaluator.evaluators[treeEvaluator.evaluators.length - 2];

		this.tmp = new int[scp.length];
		System.out.println(tree);
	}

	@Override
	public long limit() {
		return (long) node.value;
	}

	@Override
	public void setLimit(long newLimit) {
		node.value = newLimit;
		treeEvaluator.evaluators[treeEvaluator.evaluators.length - 2] = treeEvaluator.new LongEvaluator(newLimit);
	}

	@Override
	public void limit(long newLimit) {
		setLimit(newLimit);
		// assert minComputableObjectiveValue() - 1 <= newLimit && newLimit <= maxComputableObjectiveValue() + 1;
	}

	@Override
	public long minComputableObjectiveValue() {
		throw new UnsupportedOperationException("Not implemented (but only useful in an assert (deactivated here)");
	}

	@Override
	public long maxComputableObjectiveValue() {
		throw new UnsupportedOperationException("Not implemented (but only useful in an assert (deactivated here)");
	}

	@Override
	public long minCurrentObjectiveValue() {
		throw new UnsupportedOperationException("Not implemented (but currently only useful for BIVS (then being not compatible)");
	}

	@Override
	public long maxCurrentObjectiveValue() {
		throw new UnsupportedOperationException("Not implemented (but currently only useful for BIVS (then being not compatible)");
	}

	@Override
	public long objectiveValue() {
		assert Stream.of(scp).allMatch(x -> x.dom.size() == 1);
		for (int i = 0; i < scp.length; i++)
			tmp[i] = scp[i].dom.singleValue();
		return optTreeEvaluator.evaluate(tmp);
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	@Override
	public final boolean isSatisfiedBy(int[] t) {
		return treeEvaluator.evaluate(t) == 1; // recall that 1 stands for true
	}

	/**
	 * The Boolean expression tree giving the semantics of the constraint
	 */
	public XNodeParent<IVar> tree;

	/**
	 * The object that can be used to evaluate the Boolean expression tree, when values are specified for involved variables
	 */
	private IntensionStructure treeEvaluator;

	/**
	 * The object used to build a canonized form of the key of the constraint (mainly used for symmetry-breaking)
	 */
	private final KeyCanonizer keyCanonizer;

	@Override
	public int[] symmetryMatching() {
		return keyCanonizer != null ? keyCanonizer.computeSymmetryMatching() : Kit.series(1, scp.length);
	}

	@Override
	public IntensionStructure intStructure() {
		return treeEvaluator;
	}

	/**
	 * Build an Intension constraint for the specified problem from the specified Boolean expression tree, and with the specified scope
	 * 
	 * @param pb
	 *            the problem to which this constraint belongs
	 * @param scp
	 *            the scope of the constraint
	 * @param tree
	 *            the Boolean expression tree giving the semantics of the constraint
	 */
	public ConstraintIntension(Problem pb, Variable[] scp, XNodeParent<IVar> tree) {
		super(pb, scp);
		assert tree.exactlyVars(scp);
		assert Variable.haveSameType(scp) : "Currently, it is not possible to mix integer and symbolic variables";
		this.tree = tree; // canonize ? (XNodeParent<IVar>) tree.canonization() : tree;
		this.keyCanonizer = scp.length > 30 || tree.size() > 200 ? null : new KeyCanonizer(tree); // TODO hard coding
		String key = defineKey(tree.toPostfixExpression(tree.vars())); // keyCanonizer == null ? tree.toPostfixExpression(tree.vars()) : keyCanonizer.key());
																		// BUG if keyCanonizer.key() see
		Map<String, IntensionStructure> map = pb.head.structureSharing.mapForIntension;
		this.treeEvaluator = map.computeIfAbsent(key,
				s -> scp[0] instanceof VariableInteger ? new IntensionStructure(tree) : new IntensionStructure(tree, pb.symbolic.mapOfSymbols));
		control(Stream.of(treeEvaluator.evaluators).noneMatch(e -> e instanceof F1Evaluator || e instanceof F2Evaluator));
		treeEvaluator.register(this);
	}

	@Override
	public final boolean launchFiltering(Variable x) {
		if (futvars.size() > genericFilteringThreshold) {
			int nNonSingletons = 0;
			double prod = 1;
			for (int i = futvars.limit; i >= 0; i--) {
				Variable y = scp[futvars.dense[i]];
				if (y.dom.size() > 1) {
					nNonSingletons++;
					prod = prod * y.dom.size();
					if (nNonSingletons > 1 && prod > 10_000) // hard coding : if at least two unfixed variables and space > 10 000
						return true;
				}
			}
		}
		Reviser reviser = ((Forward) problem.solver.propagation).reviser;
		int nNonSingletons = 0;
		for (int i = futvars.limit; i >= 0; i--) { // we iterate over all variables because filtering was maybe incomplete before. Unless we are sure that it
													// was never possible ?
			Variable y = scp[futvars.dense[i]];
			if (reviser.revise(this, y) == false)
				return false;
			if (y.dom.size() > 1)
				nNonSingletons++;
		}
		return nNonSingletons <= 1 ? entail() : true;
	}
}

// public boolean isEligibleForSettingHugeDomainVariable() {
// if (futvars.size() != 1) return false;
// int pos = futvars.dense[0];
// if (!(scp[pos].dom instanceof DomainHuge)) return false;
// if (tree.type != TypeExpr.EQ || tree.sons.length != 2) return false;
// int g = tree.sons[0].type == TypeExpr.VAR && ((XNodeLeaf)tree.sons[0]).value == scp[pos] ? 0: tree.sons[1].type ==
// TypeExpr.VAR &&
// ((XNodeLeaf)tree.sons[1]).value == scp[pos] ? 1 : -1;
// if (g == -1) return false;
// }

// public int deduce() {
// control(futvars.size() == 1);
// int pos = futvars.dense[0];
// control(scp[pos].dom instanceof DomainHuge);
// control(tree.type == TypeExpr.EQ && tree.sons.length == 2);
// long sum = 0;
// for (int i = 0; i < scp.length; i++)
// if (i != pos)sum += scp[i].dom.uniqueValue();
// long res = limit - sum;
// control(Utilities.isSafeInt(res));
// return (int) res;
// }
