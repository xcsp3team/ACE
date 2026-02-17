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

import java.io.IOException;
import java.io.OutputStream;

import org.ojalgo.optimisation.ExpressionsBasedModel;
import org.ojalgo.optimisation.Variable;
import org.ojalgo.optimisation.Optimisation;
import org.ojalgo.optimisation.solver.cplex.SolverCPLEX;

import problem.Problem;
import constraints.Constraint;
import constraints.global.Sum;
import variables.Domain;
import utility.Kit;
import optimization.linearization.ConstraintLinearizer;
import optimization.linearization.LinearizationContext;
import optimization.linearization.SumLinearizer;
import optimization.linearization.CountLinearizer;
import optimization.linearization.ExtremumLinearizer;
import optimization.linearization.AllEqualLinearizer;
import optimization.linearization.LexicographicLinearizer;
import optimization.linearization.PrimitiveLinearizer;
import optimization.linearization.ReificationLinearizer;
import optimization.linearization.CumulativeLinearizer;
import optimization.linearization.IntensionLinearizer;

import java.util.List;
import java.util.Map;
import java.util.LinkedHashMap;
import java.util.HashMap;


/**
 * LP Relaxation for computing lower/upper bounds to enable optimality detection.
 * This is a simple implementation that only handles
 * linear constraints (Sum constraints) and relaxes variable integrality.
 *
 * The model is built once and variable domains are updated at each node to avoid
 * reconstructing the entire LP model repeatedly.
 */
public class LPRelaxation {

    /**
     * Registry of constraint linearizers.
     */
    private static final List<ConstraintLinearizer> LINEARIZERS = List.of(
        new SumLinearizer(),
        new CountLinearizer(),
        new ExtremumLinearizer(),
        new AllEqualLinearizer(),
        new LexicographicLinearizer(),
        new PrimitiveLinearizer(),
        new ReificationLinearizer(),
        new CumulativeLinearizer(),
        new IntensionLinearizer()
    );

    private final Problem problem;
    private ExpressionsBasedModel model;
    private Variable[] lpVars;  // LP variables corresponding to CP variables
    private boolean modelBuilt = false;  // Track if model structure has been built
    private org.ojalgo.optimisation.Expression boundConstraint;  // Constraint for incumbent bound (enables pruning)
    private final long lpTimeoutMs;
    private LinearizationContext context;


    /**
     * Creates an LP relaxation for the given problem.
     *
     * @param problem the problem to create LP relaxation for
     */
    public LPRelaxation(Problem problem) {
        this.problem = problem;
        this.lpTimeoutMs = problem.head.control.optimization.lpTimeoutMs;
    }

    /**
     * Build LP model structure (variables and constraints) once.
     * This creates continuous variables and adds linear constraints.
     * Variable bounds are set from initial domains and can be updated later via updateDomains().
     */
    public void buildModel() {
        if (modelBuilt) {
            // Model already built, just update domains
            updateDomains();
            return;
        }

        model = new ExpressionsBasedModel();
        variables.Variable[] cpVars = problem.variables;
        lpVars = new Variable[cpVars.length];

        // Create LP variables with initial domain bounds
        for (int i = 0; i < cpVars.length; i++) {
            Domain dom = cpVars[i].dom;
            // Use current domain bounds
            double lowerBound = dom.size() > 0 ? dom.firstValue() : 0;
            double upperBound = dom.size() > 0 ? dom.lastValue() : 0;

            lpVars[i] = Variable.make("x" + i)
                .lower(lowerBound)
                .upper(upperBound);
            model.addVariable(lpVars[i]);
        }

        context = new LinearizationContext(model, lpVars, problem);

        Constraint clb = problem.optimizer != null ? (Constraint) problem.optimizer.clb : null;
        Constraint cub = problem.optimizer != null ? (Constraint) problem.optimizer.cub : null;

        int linearConstraints = 0;
        int nonLinearConstraints = 0;

        // Statistics tracking (for verbose mode)
        Map<String, Integer> linearizerStats = new LinkedHashMap<>();
        Map<String, Integer> relaxedStats = new HashMap<>();
        for (ConstraintLinearizer lin : LINEARIZERS) {
            linearizerStats.put(lin.getClass().getSimpleName(), 0);
        }

        for (Constraint c : problem.constraints) {
            if (c.ignored) {
                continue;
            }

            // Skip the optimizer's bound constraints
            if (c == clb || c == cub) {
                continue;
            }

            String linearizerUsed = addConstraintIfLinearWithStats(c);
            if (linearizerUsed != null) {
                linearConstraints++;
                linearizerStats.merge(linearizerUsed, 1, Integer::sum);
            } else {
                nonLinearConstraints++;
                String ctrType = c.getClass().getSimpleName();
                relaxedStats.merge(ctrType, 1, Integer::sum);
            }
        }

        // Log summary
        Kit.log.config("\tLP model: " + linearConstraints + " linear constraints, " + nonLinearConstraints + " non-linear (relaxed)");
        Kit.log.config("\tLP cuts: " + context.getCoverCutCount());

        // Log detailed stats if verbose
        if (problem.head.control.general.verbose > 0) {
            int total = linearConstraints + nonLinearConstraints;
            double coverage = total > 0 ? (100.0 * linearConstraints / total) : 0;
            Kit.log.config(String.format("\tLP coverage: %.1f%% (%d/%d constraints)", coverage, linearConstraints, total));

            // Linearizer breakdown
            StringBuilder linStats = new StringBuilder("\tLP linearizers: ");
            boolean first = true;
            for (Map.Entry<String, Integer> e : linearizerStats.entrySet()) {
                if (e.getValue() > 0) {
                    if (!first) linStats.append(", ");
                    linStats.append(e.getKey().replace("Linearizer", "")).append(":").append(e.getValue());
                    first = false;
                }
            }
            Kit.log.config(linStats.toString());

            // Relaxed constraint types (if any)
            if (!relaxedStats.isEmpty() && problem.head.control.general.verbose > 0) {
                StringBuilder relStats = new StringBuilder("\tLP relaxed (not linearized): ");
                first = true;
                for (Map.Entry<String, Integer> e : relaxedStats.entrySet()) {
                    if (!first) relStats.append(", ");
                    relStats.append(e.getKey()).append(":").append(e.getValue());
                    first = false;
                }
                Kit.log.config(relStats.toString());

                // Show skipped Intension patterns (helps identify what to implement next)
                Map<String, Integer> skippedPatterns = IntensionLinearizer.getSkippedPatterns();
                if (!skippedPatterns.isEmpty()) {
                    StringBuilder patStats = new StringBuilder("\tLP skipped Intension patterns: ");
                    first = true;
                    // Sort by count descending, show top 5
                    skippedPatterns.entrySet().stream()
                        .sorted((a, b) -> b.getValue().compareTo(a.getValue()))
                        .limit(5)
                        .forEach(e -> {});
                    int shown = 0;
                    for (Map.Entry<String, Integer> e : skippedPatterns.entrySet()) {
                        if (shown >= 5) break;
                        if (!first) patStats.append(", ");
                        patStats.append(e.getKey()).append(":").append(e.getValue());
                        first = false;
                        shown++;
                    }
                    if (skippedPatterns.size() > 5) {
                        patStats.append(", ...(").append(skippedPatterns.size() - 5).append(" more)");
                    }
                    Kit.log.config(patStats.toString());
                }
            }
        }

        // Set objective (from Optimizer)
        setObjective();

        // Add bound constraint for pruning (objective <= bestKnown for minimization, >= for maximization)
        //addBoundConstraint();

        // Configure solver options (once)
        configureSolver();

        modelBuilt = true;
    }

    /**
     * Adds a constraint on the objective to enable pruning based on incumbent solution.
     * For minimization: objective <= maxBound (best known solution)
     * For maximization: objective >= minBound (best known solution)
     */
    private void addBoundConstraint() {
        if (problem.optimizer == null || !objectiveSet) {
            return;
        }

        // Create a constraint that mirrors the objective expression
        Optimizable objCtr = problem.optimizer.ctr;
        boundConstraint = model.addExpression("incumbent_bound");

        if (objCtr instanceof Sum.SumSimple.SumSimpleLE || objCtr instanceof Sum.SumSimple.SumSimpleGE) {
            Sum.SumSimple sumCtr = (Sum.SumSimple) objCtr;
            for (variables.Variable var : sumCtr.scp) {
                boundConstraint.set(lpVars[var.num], 1);
            }
        } else if (objCtr instanceof Sum.SumWeighted.SumWeightedLE || objCtr instanceof Sum.SumWeighted.SumWeightedGE) {
            Sum.SumWeighted sumCtr = (Sum.SumWeighted) objCtr;
            int[] coeffs = sumCtr.icoeffs;
            for (int i = 0; i < sumCtr.scp.length; i++) {
                boundConstraint.set(lpVars[sumCtr.scp[i].num], coeffs[i]);
            }
        } else if (objCtr instanceof ObjectiveVariable) {
            ObjectiveVariable objVar = (ObjectiveVariable) objCtr;
            boundConstraint.set(lpVars[objVar.x.num], 1);
        }

        // Set initial bound from optimizer
        if (problem.optimizer.minimization) {
            // For minimization, we want objective <= maxBound (best known - 1)
            boundConstraint.upper(problem.optimizer.maxBound);
        } else {
            // For maximization, we want objective >= minBound (best known + 1)
            boundConstraint.lower(problem.optimizer.minBound);
        }
    }

    /**
     * Update the bound constraint when a new incumbent solution is found.
     * Called by Optimizer when a better solution is discovered.
     *
     * @param newBound the new bound value (maxBound for minimization, minBound for maximization)
     */
    public void updateBound(long newBound) {
        if (boundConstraint == null) {
            return;
        }

        if (problem.optimizer.minimization) {
            boundConstraint.upper(newBound);
        } else {
            boundConstraint.lower(newBound);
        }
    }

    /**
     * Update LP variable bounds from current CP variable domains.
     * This is called at each search node instead of rebuilding the entire model.
     */
    public void updateDomains() {
        if (model == null || lpVars == null) {
            return;
        }

        variables.Variable[] cpVars = problem.variables;
        for (int i = 0; i < cpVars.length; i++) {
            Domain dom = cpVars[i].dom;
            double lowerBound = dom.size() > 0 ? dom.firstValue() : 0;
            double upperBound = dom.size() > 0 ? dom.lastValue() : 0;

            lpVars[i].lower(lowerBound);
            lpVars[i].upper(upperBound);
        }
    }

    /**
     * Adds a constraint to the LP model if it can be linearized.
     * Non-linear constraints (Element, etc.) are relaxed away (ignored).
     *
     * @param c the constraint to potentially add
     * @return true if constraint was added, false otherwise
     */
    private boolean addConstraintIfLinear(Constraint c) {
        return addConstraintIfLinearWithStats(c) != null;
    }

    /**
     * Adds a constraint to the LP model if it can be linearized.
     * Returns the name of the linearizer used, or null if not linearized.
     *
     * @param c the constraint to potentially add
     * @return the linearizer class name if successful, null otherwise
     */
    private String addConstraintIfLinearWithStats(Constraint c) {
        for (ConstraintLinearizer linearizer : LINEARIZERS) {
            if (linearizer.canLinearize(c)) {
                if (linearizer.linearize(c, context)) {
                    return linearizer.getClass().getSimpleName();
                }
            }
        }
        // No linearizer found - constraint is relaxed away
        return null;
    }

    /**
     * Flag indicating if a valid objective was set
     */
    private boolean objectiveSet = false;

    /**
     * Sets the objective function based on the optimizer constraint.
     * The optimizer's main constraint (clb or cub) defines the objective.
     */
    private void setObjective() {
        objectiveSet = false;

        if (problem.optimizer == null) {
            return;
        }

        Optimizable objCtr = problem.optimizer.ctr;

        if (objCtr instanceof Sum.SumSimple.SumSimpleLE || objCtr instanceof Sum.SumSimple.SumSimpleGE) {
            Sum.SumSimple sumCtr = (Sum.SumSimple) objCtr;
            variables.Variable[] scp = sumCtr.scp;

            // Build objective expression
            org.ojalgo.optimisation.Expression objExpr = model.addExpression("objective");
            for (variables.Variable var : scp) {
                objExpr.set(lpVars[var.num], 1);
            }

            // Set as objective (minimize or maximize based on optimizer type)
            objExpr.weight(1);
            objectiveSet = true;

        } else if (objCtr instanceof Sum.SumWeighted.SumWeightedLE || objCtr instanceof Sum.SumWeighted.SumWeightedGE) {
            Sum.SumWeighted sumCtr = (Sum.SumWeighted) objCtr;
            variables.Variable[] scp = sumCtr.scp;
            int[] coeffs = sumCtr.icoeffs;

            // Build objective expression
            org.ojalgo.optimisation.Expression objExpr = model.addExpression("objective");
            for (int i = 0; i < scp.length; i++) {
                objExpr.set(lpVars[scp[i].num], coeffs[i]);
            }

            // Set as objective
            objExpr.weight(1);
            objectiveSet = true;

        } else if (objCtr instanceof ObjectiveVariable) {
            // Handle objective variable case
            ObjectiveVariable objVar = (ObjectiveVariable) objCtr;
            int varNum = objVar.x.num;

            org.ojalgo.optimisation.Expression objExpr = model.addExpression("objective");
            objExpr.set(lpVars[varNum], 1);
            objExpr.weight(1);
            objectiveSet = true;
        }
        // If none of the above match, objectiveSet stays false
        // solve() will return null in that case
    }

    /**
     * Configure solver options. Called once during model building.
     * Note: Verbose/debug output is enabled dynamically in solve() only at root node.
     */
    private void configureSolver() {
        // Avoid numeric garbage from SolverCPLEX 3.0.x default logger stream handling.
        model.options.setConfigurator((SolverCPLEX.Configurator) (cplex, options) -> {
            try {
                cplex.setParam(ilog.cplex.IloCplex.IntParam.Threads, 1);
            } catch (Exception ignored) {
                // Keep default CPLEX thread config if setting this parameter fails.
            }
            if (options.logger_appender != null) {
                cplex.setOut(new OutputStream() {
                    @Override
                    public void write(final int b) throws IOException {
                        options.logger_appender.print((char) b);
                    }
                });
            } else {
                cplex.setOut(OutputStream.nullOutputStream());
            }
        });

        // Set time limit to prevent LP from taking too long
        // Abort LP solve when timeout is reached.
        if (lpTimeoutMs > 0L) {
            model.options.time_abort = lpTimeoutMs;
        }

        model.options.sparse = Boolean.TRUE;
        // Relax integrality constraints (make all variables continuous)
        model.relax();
    }

    /**
     * Solve the LP relaxation and return the bound value.
     * The model is reused across calls - only variable bounds are updated via updateDomains().
     *
     * @param atRoot true if solving at root node (enables verbose output with -v=1)
     * @return the LP bound value, or null if LP is infeasible/unbounded or objective not set
     */
    public Double solve(boolean atRoot) {
        if (model == null || !objectiveSet) {
            return null;
        }

        try {
            // Enable verbose LP solving at root when -v=1
            boolean verbose = problem.head.control.general.verbose > 0;
            if (atRoot && verbose) {
                model.options.progress(BoundAwareSolverCPLEX.class);
                if (problem.head.control.general.verbose > 1) {
                    model.options.debug(BoundAwareSolverCPLEX.class);
                }
            }

            long startTime = System.currentTimeMillis();

            // Minimize or maximize based on optimizer type
            Optimisation.Result result;
            synchronized (ExpressionsBasedModel.class) {
                ExpressionsBasedModel.removeIntegration(BoundAwareSolverCPLEX.INTEGRATION);
                ExpressionsBasedModel.addPreferredSolver(BoundAwareSolverCPLEX.INTEGRATION);
                try {
                    if (problem.optimizer.minimization) {
                        result = model.minimise();
                    } else {
                        result = model.maximise();
                    }
                } finally {
                    ExpressionsBasedModel.removeIntegration(BoundAwareSolverCPLEX.INTEGRATION);
                }
            }
            double bestBound = BoundAwareSolverCPLEX.getLastBestBound();

            long elapsed = System.currentTimeMillis() - startTime;
            if (verbose && ! result.getState().isFailure()) {
                String primalPart = Double.isFinite(result.getValue()) ? ", primal: " + result.getValue() : "";
                String dualPart = Double.isFinite(bestBound) ? ", bestBound: " + bestBound : "";
                Kit.log.config("LP solve time: " + elapsed + "ms, state: " + result.getState() + primalPart + dualPart);
            }

            if (result.getState().isOptimal()) {
                return result.getValue();
            }

            if (Double.isFinite(bestBound)) {
                return bestBound;
            }

            // LP infeasible means the current search branch is infeasible
            return null;

        } catch (Exception e) {
            Kit.log.config("LP solver error: " + e.getMessage() + " (" + e.getClass().getSimpleName() + ")");
            // In case of any LP solver error, return null (no bound)
            return null;
        }
    }

    /**
     * Check if LP relaxation is viable for this problem.
     * LP is not viable if the objective can't be modeled (e.g., SumViewWeighted).
     *
     * @return true if LP can provide useful bounds, false otherwise
     */
    public boolean isViable() {
        return objectiveSet;
    }
}
