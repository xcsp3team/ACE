/*
 * This file is part of the constraint solver ACE (AbsCon Essence).
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS.
 *
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package optimization;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.ojalgo.optimisation.ExpressionsBasedModel;
import org.ojalgo.optimisation.Expression;
import org.ojalgo.optimisation.Optimisation;
import org.ojalgo.optimisation.Variable;

import constraints.Constraint;
import constraints.global.Sum;
import optimization.linearization.AllEqualLinearizer;
import optimization.linearization.ConstraintLinearizer;
import optimization.linearization.CountLinearizer;
import optimization.linearization.CumulativeLinearizer;
import optimization.linearization.ExtremumLinearizer;
import optimization.linearization.IntensionLinearizer;
import optimization.linearization.LexicographicLinearizer;
import optimization.linearization.LinearizationContext;
import optimization.linearization.PrimitiveLinearizer;
import optimization.linearization.ReificationLinearizer;
import optimization.linearization.SumLinearizer;
import problem.Problem;
import utility.Kit;
import variables.Domain;

/**
 * LP relaxation used to derive valid objective bounds from the current root or
 * search subtree domains. For a continuous LP, the valid global "best bound" is
 * simply the optimal LP objective, so this class only trusts optimal solves.
 */
public final class LPRelaxation {

	public static final class SolveResult {
		public final Optimisation.State state;
		public final double objectiveValue;
		public final double[] variableValues;

		private SolveResult(Optimisation.State state, double objectiveValue, double[] variableValues) {
			this.state = state;
			this.objectiveValue = objectiveValue;
			this.variableValues = variableValues;
		}

		public boolean hasObjectiveBound() {
			return state != null && state.isOptimal();
		}

		public boolean isInfeasible() {
			return state == Optimisation.State.INFEASIBLE;
		}
	}

	private static final double ROUNDING_EPS = 1e-9;

	private static final List<ConstraintLinearizer> LINEARIZERS = List.of(
			new SumLinearizer(),
			new CountLinearizer(),
			new ExtremumLinearizer(),
			new AllEqualLinearizer(),
			new LexicographicLinearizer(),
			new PrimitiveLinearizer(),
			new ReificationLinearizer(),
			new CumulativeLinearizer(),
			new IntensionLinearizer());

	private final Problem problem;
	private final long lpTimeoutMs;

	private ExpressionsBasedModel model;
	private Variable[] lpVars;
	private LinearizationContext context;
	private boolean modelBuilt;
	private boolean objectiveSet;

	public LPRelaxation(Problem problem) {
		this.problem = problem;
		this.lpTimeoutMs = problem.head.control.optimization.lpTimeoutMs;
	}

	public void buildModel() {
		if (modelBuilt) {
			updateDomains();
			return;
		}

		model = new ExpressionsBasedModel();
		variables.Variable[] cpVars = problem.variables;
		lpVars = new Variable[cpVars.length];

		for (int i = 0; i < cpVars.length; i++) {
			Domain dom = cpVars[i].dom;
			lpVars[i] = Variable.make("x" + i).lower(dom.firstValue()).upper(dom.lastValue());
			model.addVariable(lpVars[i]);
		}

		context = new LinearizationContext(model, lpVars, problem);
		logLinearizedModel(addRelaxedConstraints());
		setObjective();
		configureModel();
		modelBuilt = true;
	}

	public boolean isViable() {
		return objectiveSet;
	}

	public void updateDomains() {
		if (lpVars == null)
			return;
		variables.Variable[] cpVars = problem.variables;
		for (int i = 0; i < cpVars.length; i++) {
			Domain dom = cpVars[i].dom;
			lpVars[i].lower(dom.firstValue());
			lpVars[i].upper(dom.lastValue());
		}
	}

	public int numOriginalVariables() {
		return problem.variables.length;
	}

	public double getVariableLowerBound(int index) {
		return lpVars[index].getUnadjustedLowerLimit();
	}

	public double getVariableUpperBound(int index) {
		return lpVars[index].getUnadjustedUpperLimit();
	}

	public void setVariableBounds(int index, double lower, double upper) {
		lpVars[index].lower(lower);
		lpVars[index].upper(upper);
	}

	public long roundObjectiveBound(double value, boolean minimization) {
		return minimization ? (long) Math.ceil(value - ROUNDING_EPS) : (long) Math.floor(value + ROUNDING_EPS);
	}

	public SolveResult solve(boolean atRoot) {
		if (model == null || !objectiveSet)
			return new SolveResult(Optimisation.State.INVALID, Double.NaN, null);

		try {
			long start = System.currentTimeMillis();
			Optimisation.Result result = problem.optimizer.minimization ? model.minimise() : model.maximise();
			Optimisation.State state = result.getState();
			long elapsed = System.currentTimeMillis() - start;

			if (problem.head.control.general.verbose > 0) {
				String location = atRoot ? "root" : "local";
				String value = state.isOptimal() ? ", objective: " + result.getValue() : "";
				Kit.log.config("LP solve (" + location + "): " + state + value + ", " + elapsed + "ms");
			}

			if (!state.isOptimal())
				return new SolveResult(state, Double.NaN, null);

			double[] values = new double[problem.variables.length];
			for (int i = 0; i < values.length; i++)
				values[i] = result.doubleValue(i);
			return new SolveResult(state, result.getValue(), values);
		} catch (Exception e) {
			Kit.log.config("LP solver error: " + e.getMessage() + " (" + e.getClass().getSimpleName() + ")");
			return new SolveResult(Optimisation.State.FAILED, Double.NaN, null);
		}
	}

	private Map<String, Integer> addRelaxedConstraints() {
		Constraint clb = problem.optimizer != null ? (Constraint) problem.optimizer.clb : null;
		Constraint cub = problem.optimizer != null ? (Constraint) problem.optimizer.cub : null;
		Map<String, Integer> stats = new LinkedHashMap<>();
		Map<String, Integer> relaxed = new HashMap<>();
		for (ConstraintLinearizer linearizer : LINEARIZERS)
			stats.put(linearizer.getClass().getSimpleName(), 0);

		int linearConstraints = 0;
		int relaxedConstraints = 0;

		for (Constraint c : problem.constraints) {
			if (c.ignored || c == clb || c == cub)
				continue;
			String linearizerUsed = addConstraintIfLinear(c);
			if (linearizerUsed != null) {
				linearConstraints++;
				stats.merge(linearizerUsed, 1, Integer::sum);
			} else {
				relaxedConstraints++;
				relaxed.merge(c.getClass().getSimpleName(), 1, Integer::sum);
			}
		}

		stats.put("__LINEAR__", linearConstraints);
		stats.put("__RELAXED__", relaxedConstraints);
		if (problem.head.control.general.verbose > 0) {
			for (Map.Entry<String, Integer> entry : relaxed.entrySet())
				stats.put("__RELAXED__" + entry.getKey(), entry.getValue());
		}
		return stats;
	}

	private String addConstraintIfLinear(Constraint c) {
		for (ConstraintLinearizer linearizer : LINEARIZERS) {
			if (linearizer.canLinearize(c) && linearizer.linearize(c, context))
				return linearizer.getClass().getSimpleName();
		}
		return null;
	}

	private void logLinearizedModel(Map<String, Integer> stats) {
		int linearConstraints = stats.remove("__LINEAR__");
		int relaxedConstraints = stats.remove("__RELAXED__");
		Kit.log.config("\tLP model: " + linearConstraints + " linear constraints, " + relaxedConstraints + " relaxed");
		Kit.log.config("\tLP cuts: " + context.getCoverCutCount());

		if (problem.head.control.general.verbose <= 0)
			return;

		int total = linearConstraints + relaxedConstraints;
		double coverage = total == 0 ? 0d : 100d * linearConstraints / total;
		Kit.log.config(String.format("\tLP coverage: %.1f%% (%d/%d constraints)", coverage, linearConstraints, total));

		StringBuilder linStats = new StringBuilder("\tLP linearizers: ");
		boolean first = true;
		for (Map.Entry<String, Integer> entry : stats.entrySet()) {
			if (entry.getKey().startsWith("__RELAXED__") || entry.getValue() <= 0)
				continue;
			if (!first)
				linStats.append(", ");
			linStats.append(entry.getKey().replace("Linearizer", "")).append(":").append(entry.getValue());
			first = false;
		}
		if (!first)
			Kit.log.config(linStats.toString());

		StringBuilder relaxedStats = new StringBuilder("\tLP relaxed (not linearized): ");
		first = true;
		for (Map.Entry<String, Integer> entry : stats.entrySet()) {
			if (!entry.getKey().startsWith("__RELAXED__"))
				continue;
			if (!first)
				relaxedStats.append(", ");
			relaxedStats.append(entry.getKey().substring("__RELAXED__".length())).append(":").append(entry.getValue());
			first = false;
		}
		if (!first)
			Kit.log.config(relaxedStats.toString());

		Map<String, Integer> skippedPatterns = IntensionLinearizer.getSkippedPatterns();
		if (skippedPatterns.isEmpty())
			return;
		StringBuilder patternStats = new StringBuilder("\tLP skipped Intension patterns: ");
		first = true;
		int shown = 0;
		for (Map.Entry<String, Integer> entry : skippedPatterns.entrySet()) {
			if (shown == 5)
				break;
			if (!first)
				patternStats.append(", ");
			patternStats.append(entry.getKey()).append(":").append(entry.getValue());
			first = false;
			shown++;
		}
		if (skippedPatterns.size() > shown)
			patternStats.append(", ...(").append(skippedPatterns.size() - shown).append(" more)");
		Kit.log.config(patternStats.toString());
	}

	private void setObjective() {
		objectiveSet = false;
		if (problem.optimizer == null)
			return;

		Optimizable objective = problem.optimizer.ctr;
		Expression objExpr = model.addExpression("objective");

		if (objective instanceof Sum.SumSimple.SumSimpleLE || objective instanceof Sum.SumSimple.SumSimpleGE) {
			for (variables.Variable var : ((Sum.SumSimple) objective).scp)
				objExpr.set(lpVars[var.num], 1);
			objExpr.weight(1);
			objectiveSet = true;
		} else if (objective instanceof Sum.SumWeighted.SumWeightedLE || objective instanceof Sum.SumWeighted.SumWeightedGE) {
			Sum.SumWeighted sumCtr = (Sum.SumWeighted) objective;
			for (int i = 0; i < sumCtr.scp.length; i++)
				objExpr.set(lpVars[sumCtr.scp[i].num], sumCtr.icoeffs[i]);
			objExpr.weight(1);
			objectiveSet = true;
		} else if (objective instanceof ObjectiveVariable) {
			objExpr.set(lpVars[((ObjectiveVariable) objective).x.num], 1);
			objExpr.weight(1);
			objectiveSet = true;
		}
	}

	private void configureModel() {
		if (lpTimeoutMs > 0L)
			model.options.time_abort = lpTimeoutMs;
		model.options.sparse = Boolean.TRUE;
		model.relax();
	}
}
