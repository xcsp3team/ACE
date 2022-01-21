/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints;

import static utility.Kit.control;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import org.xcsp.common.IVar;
import org.xcsp.common.predicates.TreeEvaluator;
import org.xcsp.common.predicates.TreeEvaluator.F1Evaluator;
import org.xcsp.common.predicates.TreeEvaluator.F2Evaluator;
import org.xcsp.common.predicates.XNodeParent;

import constraints.intension.KeyCanonizer;
import interfaces.ConstraintRegister;
import interfaces.Tags.TagCallCompleteFiltering;
import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.Variable.VariableInteger;

/**
 * The abstract class representing Intension constraints, which are constraints whose semantics is given by a Boolean
 * expression tree involving variables. Most of the times, primitives are used instead of this general form.
 * 
 * @author Christophe Lecoutre
 */
public final class ConstraintIntension extends Constraint implements TagCallCompleteFiltering {

	/**********************************************************************************************
	 * Intern class
	 *********************************************************************************************/

	/**
	 * The structure for managing Boolean expression trees. This is basically a tree evaluator with additional
	 * information concerning which constraints share the same structures.
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
		 * Builds an intension structure for the specified Boolean expression tree, while using the specified map of
		 * symbols because symbolic variables are involved
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
	 * The object that can be used to evaluate the Boolean expression tree, when values are specified for involved
	 * variables
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
	 * Build an Intension constraint for the specified problem from the specified Boolean expression tree, and with the
	 * specified scope
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
		String key = defineKey(keyCanonizer == null ? tree.toPostfixExpression(tree.vars()) : keyCanonizer.key());
		Map<String, IntensionStructure> map = pb.head.structureSharing.mapForIntension;
		this.treeEvaluator = map.computeIfAbsent(key,
				s -> scp[0] instanceof VariableInteger ? new IntensionStructure(tree) : new IntensionStructure(tree, pb.symbolic.mapOfSymbols));
		control(Stream.of(treeEvaluator.evaluators).noneMatch(e -> e instanceof F1Evaluator || e instanceof F2Evaluator));
		treeEvaluator.register(this);
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
