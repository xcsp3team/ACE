package constraints.intension;

import java.util.Arrays;
import java.util.Stack;

import org.xcsp.common.Constants;
import org.xcsp.common.IVar;
import org.xcsp.common.Types;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.TreeEvaluator;
import org.xcsp.common.predicates.XNodeParent;

import utility.Kit;

public final class KeyCanonizer {

	private static final String SUB_ABS = "subabs";

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
	 * @return the canonical form of the initially specified tree expressio
	 */
	public String key() {
		return root.toString();
	}

	private final class Node implements Comparable<Node> {

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

		private Node(String label) {
			this.label = label;
			this.sons = new Node[0];
		}

		private Node(String label, Node son) {
			this.label = label;
			this.sons = new Node[] { son };
		}

		private Node(String label, Node[] sons) {
			this.label = label;
			this.sons = sons;
		}

		private Node cloneUnderPermutation(String label1, String label2) {
			if (sons.length == 0)
				return label.equals(label1) ? new Node(label2) : label.equals(label2) ? new Node(label1) : new Node(label);
			Node[] newSons = new Node[sons.length];
			for (int i = 0; i < sons.length; i++)
				newSons[i] = sons[i].cloneUnderPermutation(label1, label2);
			return new Node(label, newSons);
		}

		private void renderCanonical() {
			if (sons.length != 0) {
				for (Node son : sons)
					son.renderCanonical();
				if (label.equals(SUB_ABS) || TreeEvaluator.isSymmetric(label))
					Arrays.sort(sons);
				else if (sons.length == 2) {
					TypeConditionOperatorRel operator = label == null ? null : Types.valueOf(TypeConditionOperatorRel.class, label);
					if (operator != null && Utilities.isInteger(sons[0].label) && !Utilities.isInteger(sons[1].label)) {
						label = operator.arithmeticInversion().toString().toLowerCase();
						Node tmp = sons[0];
						sons[0] = sons[1];
						sons[1] = tmp;
						// TODO : just keep LT and GT by modifying limit (so as to find more equivalent expressions) ????
					}
				}
			}
		}

		private boolean isProductTerm(int[] t) {
			if (label.startsWith("%")) {
				t[Integer.parseInt(label.substring(1))] = 1;
				return true; // trival term 1*Xi
			}
			if (label.equals(TypeExpr.NEG.lcname)) {
				Kit.control(sons.length == 1 && sons[0].label.startsWith("%"));
				t[Integer.parseInt(sons[0].label.substring(1))] = -1;
				return true;
			}
			if (!label.equals(TypeExpr.MUL.lcname))
				return false;
			if (sons.length != 2)
				return false;
			if (!Utilities.isInteger(sons[1].label))
				return false;
			if (!sons[0].label.startsWith("%"))
				return false;
			t[Integer.parseInt(sons[0].label.substring(1))] = Integer.parseInt(sons[1].label);
			return true;
		}

		public int[] isSumWeighted(int size) {
			TypeConditionOperatorRel operator = label == null ? null : Types.valueOf(TypeConditionOperatorRel.class, label);
			if (operator == null)
				return null;
			if (sons.length != 2)
				return null;
			// Kit.prn("op=" + operator);
			if (!Utilities.isInteger(sons[1].label))
				return null;
			Node leftSon = sons[0];
			if (!leftSon.label.equals(TypeExpr.ADD.lcname))
				return null;
			int[] t = new int[size];
			for (int i = 0; i < leftSon.sons.length; i++)
				if (!leftSon.sons[i].isProductTerm(t))
					return null;
			return t;
		}

		public Integer isPrecedence(boolean order) {
			if (!label.equals(TypeExpr.LE.lcname))
				return null;
			if (!sons[1].label.equals("%" + (order ? 1 : 0)))
				return null;
			Node leftSon = sons[0];
			if (!leftSon.label.equals(TypeExpr.ADD.lcname))
				return null;
			if (leftSon.sons.length != 2)
				return null;
			if (!leftSon.sons[0].label.equals("%" + (order ? 0 : 1)))
				return null;
			return Kit.parseInteger(leftSon.sons[1].label);
		}

		public int[] isDisjonctive() {
			if (!label.equals(TypeExpr.OR.lcname))
				return null;
			if (sons.length != 2)
				return null;
			Integer i1 = sons[0].isPrecedence(true);
			if (i1 == null)
				return null;
			Integer i2 = sons[1].isPrecedence(false);
			if (i2 == null)
				return null;
			return new int[] { i1, i2 };
		}

		private StringBuilder toStringBuilder(StringBuilder sb) {
			for (int i = 0; i < sons.length; i++)
				sons[i].toStringBuilder(sb).append(' ');
			return sb.append(label);
		}

		public String toString() {
			return toStringBuilder(new StringBuilder()).toString();
		}
	}

	private Node buildInitialTree() {
		Stack<Node> stack = new Stack<Node>();
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
					stack.push(new Node(token, new Node[] { son1, son2 }));
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

	public KeyCanonizer(XNodeParent<IVar> tree) {
		this.tree = tree;
		this.root = buildInitialTree();
		// System.out.println(root);
		root.renderCanonical();
		// Node n = root.cloneUnderPermutation(InstanceTokens.getParameterNameFor(1), InstanceTokens.getParameterNameFor(0));
		// n.renderCanonical();
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

// int getSign() {
// if (childs.length == 0) {
// if (label.startsWith(InstanceTokens.PARAMETER_PREFIX)) {
// int id = Integer.parseInt(label.substring(InstanceTokens.PARAMETER_PREFIX.length()));
// Domain domain = involvedVariables[id].domain;
// if (domain.toValue(0) >= 0)
// return 1;
// if (domain.toValue(domain.getMaximumSize() - 1) <= 0)
// return -1;
// return 0;
// }
// Integer i = Integer.parseInt(label);
// return i >= 0 ? 1 : -1;
// }
// if (label.equals(PredicateTokens.ABS) || label.equals(SUB_ABS))
// return 1;
//
// int res = childs[0].getSign();
// if (res == 0)
// return 0;
// for (int i = 1; i < childs.length; i++) {
// if (childs[i].getSign() != res)
// return 0;
// }
// return res;
// }