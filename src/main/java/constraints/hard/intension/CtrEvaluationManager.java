/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.intension;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.xcsp.common.IVar;
import org.xcsp.common.predicates.TreeEvaluator;
import org.xcsp.common.predicates.XNodeParent;

import constraints.Constraint;
import interfaces.RegisteringCtrs;

public class CtrEvaluationManager extends TreeEvaluator implements RegisteringCtrs {

	private final List<Constraint> registeredCtrs = new ArrayList<>();

	public List<Constraint> registeredCtrs() {
		return registeredCtrs;
	}

	public CtrEvaluationManager(XNodeParent<? extends IVar> tree) {
		super(tree);
	}

	public CtrEvaluationManager(XNodeParent<? extends IVar> tree, Map<String, Integer> mapOfSymbols) {
		super(tree, mapOfSymbols);
	}
}