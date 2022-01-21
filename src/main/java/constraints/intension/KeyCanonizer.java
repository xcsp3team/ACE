/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.intension;

import java.util.Arrays;
import java.util.Stack;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.IVar;
import org.xcsp.common.Types;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.TreeEvaluator;
import org.xcsp.common.predicates.XNodeParent;

import utility.Kit;

/**
 * A class useful to compute canonical forms of intension constraints. This is useful for example for symmetry-breaking.
 *
 * @author Christophe Lecoutre
 */
public final class KeyCanonizer {

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
