/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard;

import static org.xcsp.modeler.definitions.IRootForCtrAndObj.map;

import java.util.Map;
import java.util.stream.Stream;

import org.xcsp.common.IVar;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.TreeEvaluator.Evaluator;
import org.xcsp.common.predicates.TreeEvaluator.F1Evaluator;
import org.xcsp.common.predicates.TreeEvaluator.F2Evaluator;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.definitions.ICtr.ICtrIntension;

import constraints.CtrHard;
import constraints.hard.intension.CanonicalExpressionParser;
import constraints.hard.intension.CtrEvaluationManager;
import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.VariableInteger;
import variables.VariableSymbolic;

public final class CtrIntension extends CtrHard implements ICtrIntension {

	public XNodeParent<IVar> tree;

	public CtrEvaluationManager evaluationManager;

	private CanonicalExpressionParser cep;

	private boolean canonize = false; // hard coding

	@Override
	public int[] defineSymmetryMatching() {
		return cep != null ? cep.computeSymmetryMatching() : Kit.range(1, scp.length);
	}

	private void defineKey() {
		cep = null;
		if (scp.length > 30 || tree.size() > 200) { // TODO hard coding {
			this.key = signature().append(' ').append(tree.toPostfixExpression(tree.vars())).toString();
		} else
			this.key = signature().append(' ').append((cep = new CanonicalExpressionParser(tree)).key()).toString();
	}

	public CtrIntension(Problem pb, Variable[] scp, XNodeParent<IVar> tree) {
		super(pb, scp);
		this.tree = canonize ? (XNodeParent<IVar>) tree.canonization() : tree;
		// Kit.control(tree.exactlyVars(scp));
		Kit.control(Stream.of(scp).allMatch(x -> x instanceof VariableInteger) || Stream.of(scp).allMatch(x -> x instanceof VariableSymbolic));
		defineKey();
		if (!pb.rs.mapOfEvaluationManagers.containsKey(key)) {
			evaluationManager = scp[0] instanceof VariableInteger ? new CtrEvaluationManager(tree) : new CtrEvaluationManager(tree, pb.symbolic.mapOfSymbols);
			evaluationManager.register(this);
			conflictsStructure = ConflictsStructure.build(this); // potentially null
			pb.rs.mapOfEvaluationManagers.put(key, evaluationManager);
		} else {
			evaluationManager = pb.rs.mapOfEvaluationManagers.get(key);
			evaluationManager.register(this);
			conflictsStructure = evaluationManager.firstRegisteredCtr().conflictsStructure();
			if (conflictsStructure != null)
				conflictsStructure.register(this);
			else
				conflictsStructure = ConflictsStructure.build(this);
		}
	}

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		for (Evaluator evaluator : evaluationManager.evaluators)
			if (evaluator instanceof F1Evaluator)
				((F1Evaluator) evaluator).function = pb.stuff.externFunctionArity1;
			else if (evaluator instanceof F2Evaluator)
				((F2Evaluator) evaluator).function = pb.stuff.externFunctionArity2;
	}

	public void updateWithLessThanOrEqual(Variable v1, Variable v2) {
		Kit.control(scp.length == 2 && Utilities.indexOf(v1, scp) != -1 && Utilities.indexOf(v2, scp) != -1);
		setId(explicitId() == null ? null : explicitId() + "_modified");
		this.tree = pb.api.and(tree, pb.api.le(v1, v2));
		Kit.control(tree.exactlyVars(scp));
		defineKey();

		// this.key += " " + Kit.join(universalFragmentPredicateExpression) + " " + TypeExpr.AND.lcname;
		evaluationManager.unregister(this);
		if (conflictsStructure != null)
			conflictsStructure.unregister(this);
		// String[] t = new String[canonicalPredicate.length + universalFragmentPredicateExpression.length + 1];
		// for (int i = 0; i < canonicalPredicate.length; i++)
		// t[i] = canonicalPredicate[i];
		// for (int i = canonicalPredicate.length; i < t.length - 1; i++)
		// t[i] = universalFragmentPredicateExpression[i - canonicalPredicate.length];
		// t[t.length - 1] = TypeExpr.AND.lcname;
		// this.canonicalPredicate = t;
		if (!pb.rs.mapOfEvaluationManagers.containsKey(key)) {
			evaluationManager = scp[0] instanceof VariableInteger ? new CtrEvaluationManager(tree) : new CtrEvaluationManager(tree, pb.symbolic.mapOfSymbols);
			evaluationManager.register(this);
			conflictsStructure = ConflictsStructure.build(this);
			pb.rs.mapOfEvaluationManagers.put(key, evaluationManager);
		} else {
			evaluationManager = pb.rs.mapOfEvaluationManagers.get(key);
			evaluationManager.register(this);
			conflictsStructure = evaluationManager.firstRegisteredCtr().conflictsStructure();
			if (conflictsStructure != null)
				conflictsStructure.register(this);
		}
		// updatePredicateExpression(new String[] { "%" + positionOf(v2), "%" + positionOf(v1), TypeExpr.LE.lcname });
	}

	@Override
	public final boolean checkValues(int[] vals) {
		return evaluationManager.evaluate(vals) == 1;
	}

	@Override
	public Map<String, Object> mapXCSP() {
		return map(SCOPE, scp, FUNCTION, tree);
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
