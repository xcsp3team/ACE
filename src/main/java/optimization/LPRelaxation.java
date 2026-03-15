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

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.ojalgo.optimisation.ExpressionsBasedModel;
import org.ojalgo.optimisation.Expression;
import org.ojalgo.optimisation.Optimisation;
import org.ojalgo.optimisation.Variable;
import org.ojalgo.structure.Access1D;

import constraints.Constraint;
import constraints.global.Extremum.ExtremumCst.MaximumCst;
import constraints.global.Extremum.ExtremumCst.MinimumCst;
import constraints.global.Sum;
import optimization.linearization.AllDifferentLinearizer;
import optimization.linearization.AllEqualLinearizer;
import optimization.linearization.ConstraintLinearizer;
import optimization.linearization.CountLinearizer;
import optimization.linearization.CumulativeLinearizer;
import optimization.linearization.ExtremumLinearizer;
import optimization.linearization.IntensionLinearizer;
import optimization.linearization.LexicographicLinearizer;
import optimization.linearization.LpCutGenerator;
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

	public static final String REDUCED_COSTS_PROPERTY = "ace.lp.reduced_costs";

	public static final class SolveResult {
		public final Optimisation.State state;
		public final double objectiveValue;
		public final double[] variableValues;
		public final double[] reducedCosts;

		private SolveResult(Optimisation.State state, double objectiveValue, double[] variableValues, double[] reducedCosts) {
			this.state = state;
			this.objectiveValue = objectiveValue;
			this.variableValues = variableValues;
			this.reducedCosts = reducedCosts;
		}

		public boolean hasObjectiveBound() {
			return state != null && state.isOptimal();
		}

		public boolean hasReducedCosts() {
			return reducedCosts != null;
		}

		public boolean isInfeasible() {
			return state == Optimisation.State.INFEASIBLE;
		}
	}

	public static final class ReducedCostStats {
		public final boolean enabled;
		public final long rounds;
		public final long tightenings;
		public final long valuesRemoved;
		public final long wipeouts;
		public final long reoptimizations;
		public final long improvingReoptimizations;

		private ReducedCostStats(boolean enabled, long rounds, long tightenings, long valuesRemoved, long wipeouts, long reoptimizations,
				long improvingReoptimizations) {
			this.enabled = enabled;
			this.rounds = rounds;
			this.tightenings = tightenings;
			this.valuesRemoved = valuesRemoved;
			this.wipeouts = wipeouts;
			this.reoptimizations = reoptimizations;
			this.improvingReoptimizations = improvingReoptimizations;
		}
	}

	private static final class ReducedCostFixingOutcome {
		final boolean consistent;
		final int tightenings;

		ReducedCostFixingOutcome(boolean consistent, int tightenings) {
			this.consistent = consistent;
			this.tightenings = tightenings;
		}
	}

	private static final class ReducedCostReflection {
		final Class<?> simplexSolverClass;
		final Method intermediateGetSolver;
		final Field simplexTableauField;
		final Method tableauCountConstraints;
		final Method tableauCountProblemVariables;
		final Method tableauSliceRow;

		ReducedCostReflection() throws ReflectiveOperationException {
			this.simplexSolverClass = Class.forName("org.ojalgo.optimisation.linear.SimplexSolver");
			Class<?> simplexTableauClass = Class.forName("org.ojalgo.optimisation.linear.SimplexTableau");
			this.intermediateGetSolver = findMethod(ExpressionsBasedModel.Intermediate.class, "getSolver");
			this.simplexTableauField = findField(simplexSolverClass, "myTableau");
			this.tableauCountConstraints = findMethod(simplexTableauClass, "countConstraints");
			this.tableauCountProblemVariables = findMethod(simplexTableauClass, "countProblemVariables");
			this.tableauSliceRow = findMethod(simplexTableauClass, "sliceTableauRow", int.class);
		}
	}

	private static final double ROUNDING_EPS = 1e-9;
	private static final double LP_BOUND_EPS = 1e-6;
	private static final double REDUCED_COST_EPS = 1e-9;
	private static final int MAX_CUT_ROUNDS = 3;
	private static final int MAX_REDUCED_COST_ROUNDS = 3;
	private static final ReducedCostReflection REDUCED_COST_REFLECTION = buildReducedCostReflection();

	private static final List<ConstraintLinearizer> LINEARIZERS = List.of(
			new AllDifferentLinearizer(),
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
	private final boolean reducedCostFixingEnabled;

	private ExpressionsBasedModel model;
	private ExpressionsBasedModel.Intermediate intermediate;
	private Variable[] lpVars;
	private LinearizationContext context;
	// TODO: Port more cut generators here:
	// no_overlap via DisjonctiveReified (noOverlapAux), lin_max.
	// TODO: use reduced costs not only for domain tightening, but also for
	// proof explanations / branch compression in the LB tree, like CP-SAT.
	private List<LpCutGenerator> cutGenerators;
	private boolean modelBuilt;
	private boolean objectiveSet;
	private boolean fullyLinearizedConstraints;
	private long reducedCostRounds;
	private long reducedCostTightenings;
	private long reducedCostValuesRemoved;
	private long reducedCostWipeouts;
	private long reducedCostReoptimizations;
	private long reducedCostImprovingReoptimizations;

	public LPRelaxation(Problem problem) {
		this.problem = problem;
		this.lpTimeoutMs = problem.head.control.optimization.lpTimeoutMs;
		this.reducedCostFixingEnabled = Boolean.parseBoolean(System.getProperty(REDUCED_COSTS_PROPERTY, "true"));
	}

	public void buildModel() {
		model = new ExpressionsBasedModel();
		intermediate = null;
		variables.Variable[] cpVars = problem.variables;
		lpVars = new Variable[cpVars.length];

		for (int i = 0; i < cpVars.length; i++) {
			Domain dom = cpVars[i].dom;
			lpVars[i] = Variable.make("x" + i).lower(dom.firstValue()).upper(dom.lastValue());
			model.addVariable(lpVars[i]);
		}

		context = new LinearizationContext(model, lpVars, problem);
		Map<String, Integer> stats = addRelaxedConstraints();
		cutGenerators = context.getCutGenerators();
		fullyLinearizedConstraints = stats.get("__RELAXED__") == 0;
		logLinearizedModel(stats);
		setObjective();
		configureModel();
		intermediate = model.prepare();
		modelBuilt = true;
	}

	public boolean isViable() {
		return objectiveSet;
	}

	public boolean isFullyLinearizedConstraints() {
		return objectiveSet && fullyLinearizedConstraints;
	}

	public boolean isReducedCostFixingEnabled() {
		return reducedCostFixingEnabled;
	}

	public ReducedCostStats reducedCostStats() {
		return new ReducedCostStats(reducedCostFixingEnabled, reducedCostRounds, reducedCostTightenings, reducedCostValuesRemoved, reducedCostWipeouts,
				reducedCostReoptimizations, reducedCostImprovingReoptimizations);
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
		if (intermediate != null)
			intermediate.reset();
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
		if (intermediate != null)
			intermediate.reset();
	}

	public long roundObjectiveBound(double value, boolean minimization) {
		return minimization ? (long) Math.ceil(value - ROUNDING_EPS) : (long) Math.floor(value + ROUNDING_EPS);
	}

	public SolveResult solve(boolean atRoot) {
		if (model == null || !objectiveSet)
			return new SolveResult(Optimisation.State.INVALID, Double.NaN, null, null);

		try {
			long start = System.currentTimeMillis();
			Optimisation.Result result = optimizeModel();
			Optimisation.State state = result.getState();
			if (!state.isOptimal())
				return new SolveResult(state, Double.NaN, null, null);

			double[] values = extractValues(result);
			double[] reducedCosts = extractReducedCosts();
			int generatedCuts = separateCuts(values);
			if (generatedCuts > 0) {
				result = optimizeModel();
				state = result.getState();
				if (!state.isOptimal())
					return new SolveResult(state, Double.NaN, null, null);
				values = extractValues(result);
				reducedCosts = extractReducedCosts();
			}

			long elapsed = System.currentTimeMillis() - start;
			if (problem.head.control.general.verbose > 0) {
				String location = atRoot ? "root" : "local";
				String value = state.isOptimal() ? ", objective: " + result.getValue() : "";
				String cuts = generatedCuts > 0 ? ", cuts: " + generatedCuts : "";
				Kit.log.config("LP solve (" + location + "): " + state + value + cuts + ", " + elapsed + "ms");
			}
			return new SolveResult(state, result.getValue(), values, reducedCosts);
		} catch (Exception e) {
			Kit.log.config("LP solver error: " + e.getMessage() + " (" + e.getClass().getSimpleName() + ")");
			return new SolveResult(Optimisation.State.FAILED, Double.NaN, null, null);
		}
	}

	public SolveResult solveWithReducedCostFixing(boolean atRoot, long cutoff, boolean minimization) {
		SolveResult result = solve(atRoot);
		if (!reducedCostFixingEnabled || !hasFiniteCutoff(cutoff, minimization))
			return result;

		int totalTightenings = 0;
		for (int round = 0; round < MAX_REDUCED_COST_ROUNDS; round++) {
			if (!result.hasObjectiveBound() || !result.hasReducedCosts())
				break;

			ReducedCostFixingOutcome fixing = applyReducedCostFixing(result, cutoff, minimization);
			if (!fixing.consistent)
				return new SolveResult(Optimisation.State.INFEASIBLE, Double.NaN, null, null);
			if (fixing.tightenings == 0)
				break;

			reducedCostRounds++;
			reducedCostReoptimizations++;
			totalTightenings += fixing.tightenings;
			double previousObjective = result.objectiveValue;
			updateDomains();
			result = solve(atRoot);
			if (result.hasObjectiveBound() && improvedObjective(result.objectiveValue, previousObjective, minimization))
				reducedCostImprovingReoptimizations++;
		}

		if (totalTightenings > 0 && problem.head.control.general.verbose > 0)
			Kit.log.config("LP reduced-cost tightenings: " + totalTightenings);
		return result;
	}

	private Optimisation.Result optimizeModel() {
		if (problem.optimizer.minimization)
			model.setMinimisation();
		else
			model.setMaximisation();
		if (intermediate == null)
			intermediate = model.prepare();
		return intermediate.solve(null);
	}

	private double[] extractValues(Optimisation.Result result) {
		double[] values = new double[Math.toIntExact(model.countVariables())];
		for (int i = 0; i < values.length; i++)
			values[i] = result.doubleValue(i);
		return values;
	}

	private int separateCuts(double[] values) {
		if (cutGenerators == null || cutGenerators.isEmpty())
			return 0;

		int totalCuts = 0;
		double[] currentValues = values;
		for (int round = 0; round < MAX_CUT_ROUNDS; round++) {
			int roundCuts = 0;
			var cutContext = context.cutGenerationContext(currentValues);
			for (LpCutGenerator cutGenerator : cutGenerators)
				roundCuts += cutGenerator.generateCuts(cutContext);
			if (roundCuts == 0)
				break;
			totalCuts += roundCuts;
			if (intermediate != null)
				intermediate.reset();

			Optimisation.Result result = optimizeModel();
			if (!result.getState().isOptimal())
				break;
			currentValues = extractValues(result);
		}
		return totalCuts;
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
		Kit.log.config("\tLP cut generators: " + context.getCutGeneratorCount());
		Kit.log.config("\tLP cuts: " + context.getGeneratedCutCount());

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
		} else if (objective instanceof MaximumCst) {
			setMaximumObjective((MaximumCst) objective, objExpr);
		} else if (objective instanceof MinimumCst) {
			setMinimumObjective((MinimumCst) objective, objExpr);
		}
	}

	private void setMaximumObjective(MaximumCst objective, Expression objExpr) {
		Variable maxVar = Variable.make("objective_max_" + ((Constraint) objective).num)
				.lower(objective.minCurrentObjectiveValue())
				.upper(objective.maxCurrentObjectiveValue());
		model.addVariable(maxVar);

		Expression choice = model.addExpression("objective_max_choice_" + ((Constraint) objective).num);
		for (int i = 0; i < objective.scp.length; i++) {
			variables.Variable xi = objective.scp[i];
			Expression lb = model.addExpression("objective_max_lb_" + ((Constraint) objective).num + "_" + i);
			lb.set(maxVar, 1);
			lb.set(lpVars[xi.num], -1);
			lb.lower(0);

			double m = Math.max(0d, objective.maxCurrentObjectiveValue() - xi.dom.firstValue());
			Variable zi = Variable.make("objective_max_z_" + ((Constraint) objective).num + "_" + i).lower(0).upper(1);
			model.addVariable(zi);
			choice.set(zi, 1);

			Expression ub = model.addExpression("objective_max_ub_" + ((Constraint) objective).num + "_" + i);
			ub.set(maxVar, 1);
			ub.set(lpVars[xi.num], -1);
			ub.set(zi, m);
			ub.upper(m);
		}
		choice.level(1);
		objExpr.set(maxVar, 1);
		objExpr.weight(1);
		objectiveSet = true;
	}

	private void setMinimumObjective(MinimumCst objective, Expression objExpr) {
		Variable minVar = Variable.make("objective_min_" + ((Constraint) objective).num)
				.lower(objective.minCurrentObjectiveValue())
				.upper(objective.maxCurrentObjectiveValue());
		model.addVariable(minVar);

		Expression choice = model.addExpression("objective_min_choice_" + ((Constraint) objective).num);
		for (int i = 0; i < objective.scp.length; i++) {
			variables.Variable xi = objective.scp[i];
			Expression ub = model.addExpression("objective_min_ub_" + ((Constraint) objective).num + "_" + i);
			ub.set(minVar, 1);
			ub.set(lpVars[xi.num], -1);
			ub.upper(0);

			double m = Math.max(0d, xi.dom.lastValue() - objective.minCurrentObjectiveValue());
			Variable zi = Variable.make("objective_min_z_" + ((Constraint) objective).num + "_" + i).lower(0).upper(1);
			model.addVariable(zi);
			choice.set(zi, 1);

			Expression lb = model.addExpression("objective_min_lb_" + ((Constraint) objective).num + "_" + i);
			lb.set(minVar, 1);
			lb.set(lpVars[xi.num], -1);
			lb.set(zi, -m);
			lb.lower(-m);
		}
		choice.level(1);
		objExpr.set(minVar, 1);
		objExpr.weight(1);
		objectiveSet = true;
	}

	private void configureModel() {
		if (lpTimeoutMs > 0L)
			model.options.time_abort = lpTimeoutMs;
		model.options.sparse = Boolean.TRUE;
		model.relax();
	}

	private ReducedCostFixingOutcome applyReducedCostFixing(SolveResult result, long cutoff, boolean minimization) {
		double gap = minimization ? cutoff - result.objectiveValue : result.objectiveValue - cutoff;
		if (gap < -ROUNDING_EPS)
			return new ReducedCostFixingOutcome(true, 0);

		int tightenings = 0;
		for (int i = 0; i < problem.variables.length; i++) {
			variables.Variable x = problem.variables[i];
			Domain dom = x.dom;
			if (dom.size() <= 1)
				continue;

			double value = result.variableValues[i];
			double reducedCost = result.reducedCosts[i];
			int lower = dom.firstValue();
			int upper = dom.lastValue();

				if (Math.abs(value - lower) <= LP_BOUND_EPS && reducedCost > REDUCED_COST_EPS) {
					int highestAllowed = saturatingToInt((long) lower + maxShift(gap, reducedCost));
					if (highestAllowed < upper) {
						int sizeBefore = dom.size();
						boolean consistent = dom.removeValuesGT(highestAllowed);
						if (!consistent) {
							reducedCostWipeouts++;
							return new ReducedCostFixingOutcome(false, tightenings);
						}
						reducedCostTightenings++;
						reducedCostValuesRemoved += Math.max(0, sizeBefore - dom.size());
						tightenings++;
					}
				}

			double worseningFromUpper = -reducedCost;
				if (Math.abs(value - upper) <= LP_BOUND_EPS && worseningFromUpper > REDUCED_COST_EPS) {
					int lowestAllowed = saturatingToInt((long) upper - maxShift(gap, worseningFromUpper));
					if (lowestAllowed > lower) {
						int sizeBefore = dom.size();
						boolean consistent = dom.removeValuesLT(lowestAllowed);
						if (!consistent) {
							reducedCostWipeouts++;
							return new ReducedCostFixingOutcome(false, tightenings);
						}
						reducedCostTightenings++;
						reducedCostValuesRemoved += Math.max(0, sizeBefore - dom.size());
						tightenings++;
					}
			}
		}
		return new ReducedCostFixingOutcome(true, tightenings);
	}

	private static boolean improvedObjective(double candidate, double reference, boolean minimization) {
		return minimization ? candidate > reference + LP_BOUND_EPS : candidate < reference - LP_BOUND_EPS;
	}

	private static long maxShift(double gap, double perUnitWorsening) {
		if (gap <= ROUNDING_EPS)
			return 0L;
		return Math.max(0L, (long) Math.floor((gap + ROUNDING_EPS) / perUnitWorsening));
	}

	private double[] extractReducedCosts() {
		if (REDUCED_COST_REFLECTION == null || intermediate == null)
			return null;
		try {
			Object solver = REDUCED_COST_REFLECTION.intermediateGetSolver.invoke(intermediate);
			if (solver == null || !REDUCED_COST_REFLECTION.simplexSolverClass.isInstance(solver))
				return null;
			Object tableau = REDUCED_COST_REFLECTION.simplexTableauField.get(solver);
			if (tableau == null)
				return null;
			int objectiveRow = ((Integer) REDUCED_COST_REFLECTION.tableauCountConstraints.invoke(tableau)).intValue();
			int problemVariables = ((Integer) REDUCED_COST_REFLECTION.tableauCountProblemVariables.invoke(tableau)).intValue();
			Access1D<?> row = (Access1D<?>) REDUCED_COST_REFLECTION.tableauSliceRow.invoke(tableau, objectiveRow);
			if (row == null)
				return null;

			double[] reducedCosts = new double[problem.variables.length];
			int limit = Math.min(problem.variables.length, problemVariables);
			for (int i = 0; i < limit; i++)
				reducedCosts[i] = row.doubleValue(i);
			return reducedCosts;
		} catch (ReflectiveOperationException | RuntimeException e) {
			return null;
		}
	}

	private static boolean hasFiniteCutoff(long cutoff, boolean minimization) {
		return minimization ? cutoff != Long.MAX_VALUE : cutoff != Long.MIN_VALUE;
	}

	private static ReducedCostReflection buildReducedCostReflection() {
		try {
			return new ReducedCostReflection();
		} catch (ReflectiveOperationException e) {
			return null;
		}
	}

	private static Field findField(Class<?> type, String name) throws NoSuchFieldException {
		for (Class<?> current = type; current != null; current = current.getSuperclass()) {
			try {
				Field field = current.getDeclaredField(name);
				field.setAccessible(true);
				return field;
			} catch (NoSuchFieldException e) {
				// Try parent class.
			}
		}
		throw new NoSuchFieldException(name);
	}

	private static Method findMethod(Class<?> type, String name, Class<?>... parameterTypes) throws NoSuchMethodException {
		for (Class<?> current = type; current != null; current = current.getSuperclass()) {
			try {
				Method method = current.getDeclaredMethod(name, parameterTypes);
				method.setAccessible(true);
				return method;
			} catch (NoSuchMethodException e) {
				// Try parent class.
			}
		}
		throw new NoSuchMethodException(name);
	}

	private static int saturatingToInt(long value) {
		if (value <= Integer.MIN_VALUE)
			return Integer.MIN_VALUE;
		if (value >= Integer.MAX_VALUE)
			return Integer.MAX_VALUE;
		return (int) value;
	}
}
