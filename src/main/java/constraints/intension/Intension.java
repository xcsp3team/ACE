/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.intension;

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
import org.xcsp.common.predicates.TreeEvaluator.Evaluator;
import org.xcsp.common.predicates.TreeEvaluator.F1Evaluator;
import org.xcsp.common.predicates.TreeEvaluator.F2Evaluator;
import org.xcsp.common.predicates.XNodeParent;

import constraints.Constraint;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.Variable.VariableInteger;
import variables.Variable.VariableSymbolic;

public final class Intension extends Constraint implements TagFilteringCompleteAtEachCall {

	/**********************************************************************************************
	 * Interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		for (Evaluator evaluator : treeEvaluator.evaluators)
			if (evaluator instanceof F1Evaluator)
				((F1Evaluator) evaluator).function = problem.features.externFunctionArity1;
			else if (evaluator instanceof F2Evaluator)
				((F2Evaluator) evaluator).function = problem.features.externFunctionArity2;
	}

	@Override
	public final boolean checkValues(int[] vals) {
		return treeEvaluator.evaluate(vals) == 1;
	}

	/**********************************************************************************************
	 * Intern classes
	 *********************************************************************************************/

	public static class SharedTreeEvaluator extends TreeEvaluator implements RegisteringCtrs {

		public final List<Constraint> registeredCtrs = new ArrayList<>();

		public List<Constraint> registeredCtrs() {
			return registeredCtrs;
		}

		public SharedTreeEvaluator(XNodeParent<? extends IVar> tree) {
			super(tree);
		}

		public SharedTreeEvaluator(XNodeParent<? extends IVar> tree, Map<String, Integer> mapOfSymbols) {
			super(tree, mapOfSymbols);
		}
	}

	static class KeyCanonizer {
		private static final String SUB_ABS = "subabs";

		private XNodeParent<IVar> tree;

		Node root;

		String key() {
			return root.toString();
		}

		final class Node implements Comparable<Node> {
			private String label;

			private Node[] childs;

			private Node(String label) {
				this.label = label;
				this.childs = new Node[0];
			}

			private Node(String label, Node child) {
				this.label = label;
				this.childs = new Node[] { child };
			}

			private Node(String label, Node[] childs) {
				this.label = label;
				this.childs = childs;
			}

			private Node cloneUnderPermutation(String label1, String label2) {
				if (childs.length == 0)
					return label.equals(label1) ? new Node(label2) : label.equals(label2) ? new Node(label1) : new Node(label);
				Node[] newChilds = new Node[childs.length];
				for (int i = 0; i < childs.length; i++)
					newChilds[i] = childs[i].cloneUnderPermutation(label1, label2);
				return new Node(label, newChilds);
			}

			public int compareTo(Node node) {
				if (childs.length > node.childs.length)
					return -1;
				if (childs.length < node.childs.length)
					return +1;
				if (childs.length == 0) {
					if (label.startsWith("%"))
						return Utilities.isInteger(node.label) ? -1 : label.compareTo(node.label);
					else {
						if (node.label.startsWith("%"))
							return +1;
						int i1 = Integer.parseInt(label), i2 = Integer.parseInt(node.label);
						return i1 < i2 ? -1 : i1 == i2 ? 0 : +1;
					}
				}
				if (!label.equals(node.label))
					return label.compareTo(node.label);
				for (int i = 0; i < childs.length; i++) {
					int res = childs[i].compareTo(node.childs[i]);
					if (res != 0)
						return res;
				}
				return 0;
			}

			private void renderCanonical() {
				if (childs.length != 0) {
					for (Node child : childs)
						child.renderCanonical();
					if (label.equals(SUB_ABS) || TreeEvaluator.isSymmetric(label))
						Arrays.sort(childs);
					else if (childs.length == 2) {
						TypeConditionOperatorRel operator = label == null ? null : Types.valueOf(TypeConditionOperatorRel.class, label);
						if (operator != null && Utilities.isInteger(childs[0].label) && !Utilities.isInteger(childs[1].label)) {
							label = operator.arithmeticInversion().toString().toLowerCase();
							Node tmp = childs[0];
							childs[0] = childs[1];
							childs[1] = tmp;
							// tODO : just keep LT et GT by modifying limit ????
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
					Kit.control(childs.length == 1 && childs[0].label.startsWith("%"));
					t[Integer.parseInt(childs[0].label.substring(1))] = -1;
					return true;
				}
				if (!label.equals(TypeExpr.MUL.lcname))
					return false;
				if (childs.length != 2)
					return false;
				if (!Utilities.isInteger(childs[1].label))
					return false;
				if (!childs[0].label.startsWith("%"))
					return false;
				t[Integer.parseInt(childs[0].label.substring(1))] = Integer.parseInt(childs[1].label);
				return true;
			}

			public int[] isSumWeighted(int size) {
				TypeConditionOperatorRel operator = label == null ? null : Types.valueOf(TypeConditionOperatorRel.class, label);
				if (operator == null)
					return null;
				if (childs.length != 2)
					return null;
				// Kit.prn("op=" + operator);
				if (!Utilities.isInteger(childs[1].label))
					return null;
				Node leftChild = childs[0];
				if (!leftChild.label.equals(TypeExpr.ADD.lcname))
					return null;
				int[] t = new int[size];
				for (int i = 0; i < leftChild.childs.length; i++)
					if (!leftChild.childs[i].isProductTerm(t))
						return null;
				return t;
			}

			public Integer isPrecedence(boolean order) {
				if (!label.equals(TypeExpr.LE.lcname))
					return null;
				if (!childs[1].label.equals("%" + (order ? 1 : 0)))
					return null;
				Node leftChild = childs[0];
				if (!leftChild.label.equals(TypeExpr.ADD.lcname))
					return null;
				if (leftChild.childs.length != 2)
					return null;
				if (!leftChild.childs[0].label.equals("%" + (order ? 0 : 1)))
					return null;
				return Kit.parseInteger(leftChild.childs[1].label);
			}

			public int[] isDisjonctive() {
				if (!label.equals(TypeExpr.OR.lcname))
					return null;
				if (childs.length != 2)
					return null;
				Integer i1 = childs[0].isPrecedence(true);
				if (i1 == null)
					return null;
				Integer i2 = childs[1].isPrecedence(false);
				if (i2 == null)
					return null;
				return new int[] { i1, i2 };
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

			private StringBuilder toStringBuilder(StringBuilder sb) {
				for (int i = 0; i < childs.length; i++)
					childs[i].toStringBuilder(sb).append(' ');
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
					Node child = stack.pop();
					if (token.equals(TypeExpr.ABS.lcname) && child.label.equals(TypeExpr.SUB.lcname)) {
						child.label = SUB_ABS;
						stack.push(child);
					} else
						stack.push(new Node(token, child));
				} else if (arity == 2) {
					Node child2 = stack.pop();
					Node child1 = stack.pop();
					if (TreeEvaluator.isSymmetric(token) && Utilities.isInteger(child1.label) && !Utilities.isInteger(child2.label)) {
						Node tmp = child1;
						child1 = child2;
						child2 = tmp;
					}
					if (TreeEvaluator.isAssociative(token) && (child2.label.equals(token) || child1.label.equals(token))) {
						Node[] childs = new Node[(child2.label.equals(token) ? child2.childs.length : 1)
								+ (child1.label.equals(token) ? child1.childs.length : 1)];
						int cnt = 0;
						if (child2.label.equals(token))
							for (Node child : child2.childs)
								childs[cnt++] = child;
						else
							childs[cnt++] = child2;
						if (child1.label.equals(token))
							for (Node child : child1.childs)
								childs[cnt++] = child;
						else
							childs[cnt++] = child1;
						stack.push(new Node(token, childs));

					} else {
						stack.push(new Node(token, new Node[] { child1, child2 }));
					}
				} else { // if (arity == 3) {
					Node[] childs = new Node[arity];
					for (int j = arity - 1; j >= 0; j--)
						childs[j] = stack.pop();
					stack.push(new Node(token, childs));
					// Node child3 = stack.pop();
					// Node child2 = stack.pop();
					// Node child1 = stack.pop();
					// stack.push(new Node(token, new Node[] { child1, child2, child3 }));
				}
			}
			assert stack.size() == 1;
			return stack.pop();
		}

		KeyCanonizer(XNodeParent<IVar> tree) {
			this.tree = tree;
			this.root = buildInitialTree();
			// System.out.println(root);
			root.renderCanonical();
			// Node n = root.cloneUnderPermutation(InstanceTokens.getParameterNameFor(1),
			// InstanceTokens.getParameterNameFor(0)); n.renderCanonical();
		}

		int[] computeSymmetryMatching() {
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
	 * Fields and methods
	 *********************************************************************************************/

	public XNodeParent<IVar> tree;

	public SharedTreeEvaluator treeEvaluator;

	private KeyCanonizer keyCanonizer;

	private boolean canonize = false; // TODO hard coding

	@Override
	public int[] defineSymmetryMatching() {
		return keyCanonizer != null ? keyCanonizer.computeSymmetryMatching() : Kit.range(1, scp.length);
	}

	public Intension(Problem pb, Variable[] scp, XNodeParent<IVar> tree) {
		super(pb, scp);
		this.tree = canonize ? (XNodeParent<IVar>) tree.canonization() : tree;
		// Kit.control(tree.exactlyVars(scp));
		Kit.control(Stream.of(scp).allMatch(x -> x instanceof VariableInteger) || Stream.of(scp).allMatch(x -> x instanceof VariableSymbolic));
		this.keyCanonizer = scp.length > 30 || tree.size() > 200 ? null : new KeyCanonizer(tree); // TODO hard coding (unbuilt if too costly)
		this.key = signature().append(' ').append(keyCanonizer == null ? tree.toPostfixExpression(tree.vars()) : keyCanonizer.key()).toString();

		Map<String, SharedTreeEvaluator> map = pb.head.mapOfTreeEvaluators;
		treeEvaluator = map.get(key);
		if (treeEvaluator == null) {
			treeEvaluator = scp[0] instanceof VariableInteger ? new SharedTreeEvaluator(tree) : new SharedTreeEvaluator(tree, pb.symbolic.mapOfSymbols);
			treeEvaluator.register(this);
			map.put(key, treeEvaluator);
		} else
			treeEvaluator.register(this);
	}

	// public boolean isEligibleForSettingHugeDomainVariable() {
	// if (futvars.size() != 1)
	// return false;
	// int pos = futvars.dense[0];
	// if (!(scp[pos].dom instanceof DomainHuge))
	// return false;
	// if (tree.type != TypeExpr.EQ || tree.sons.length != 2)
	// return false;
	// int g = tree.sons[0].type == TypeExpr.VAR && ((XNodeLeaf)tree.sons[0]).value == scp[pos] ? 0: tree.sons[1].type == TypeExpr.VAR &&
	// ((XNodeLeaf)tree.sons[1]).value == scp[pos] ? 1 : -1;
	// if (g == -1)
	// return false;
	//
	//
	// }

	// public int deduce() {
	//
	// Kit.control(futvars.size() == 1);
	// int pos = futvars.dense[0];
	// Kit.control(scp[pos].dom instanceof DomainHuge);
	// Kit.control(tree.type == TypeExpr.EQ && tree.sons.length == 2);
	//
	// long sum = 0;
	// for (int i = 0; i < scp.length; i++)
	// if (i != pos)
	// sum += scp[i].dom.uniqueValue();
	// long res = limit - sum;
	// Kit.control(Utilities.isSafeInt(res));
	// return (int) res;
	// }

	// public DefXCSP defXCSP() {
	// return ICtrIntension.super.defXCSP();
	// }
}
