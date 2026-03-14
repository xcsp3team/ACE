/*
 * This file is part of the constraint solver ACE (AbsCon Essence).
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS.
 *
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package optimization.linearization;

import org.ojalgo.optimisation.Expression;
import org.ojalgo.optimisation.Variable;

import problem.Problem;
import variables.Domain;

/**
 * Context exposed to cut generators after an LP solve.
 */
public final class CutGenerationContext {

	private final LinearizationContext linearizationContext;
	private final double[] lpValues;

	CutGenerationContext(LinearizationContext linearizationContext, double[] lpValues) {
		this.linearizationContext = linearizationContext;
		this.lpValues = lpValues;
	}

	public Expression addExpression(String name) {
		return linearizationContext.addExpression(name);
	}

	public Variable getLpVar(variables.Variable cpVar) {
		return linearizationContext.getLpVar(cpVar);
	}

	public Variable getLpVar(int index) {
		return linearizationContext.getLpVar(index);
	}

	public double getLpValue(variables.Variable cpVar) {
		return lpValues[cpVar.num];
	}

	public double getLpValue(int index) {
		return lpValues[index];
	}

	public boolean isBinary01Domain(Domain dom) {
		return linearizationContext.isBinary01Domain(dom);
	}

	public Problem getProblem() {
		return linearizationContext.getProblem();
	}

	public int nextGeneratedCutId() {
		return linearizationContext.nextGeneratedCutId();
	}
}
