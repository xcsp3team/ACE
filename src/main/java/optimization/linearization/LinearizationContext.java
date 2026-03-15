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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

import org.ojalgo.optimisation.ExpressionsBasedModel;
import org.ojalgo.optimisation.Variable;
import org.ojalgo.optimisation.Expression;

import problem.Problem;
import variables.Domain;

/**
 * Context object passed to ConstraintLinearizers during linearization.
 * Provides access to the LP model, variables, and helper methods.
 *
 * This class acts as a facade, shielding linearizers from the details of
 * how the LP model is structured and providing convenient utility methods.
 */
public class LinearizationContext {

    private final ExpressionsBasedModel model;
    private final Variable[] lpVars;
    private final Problem problem;
    private final List<LpCutGenerator> cutGenerators;
    private final Map<Variable, Integer> variableIndexes;
    private final Map<String, Object> metadata;
    private int generatedCutCount;

    /**
     * Creates a new linearization context.
     *
     * @param model the ojAlgo expressions-based model
     * @param lpVars LP variables corresponding to CP variables (indexed by var.num)
     * @param problem the CP problem being relaxed
     */
    public LinearizationContext(ExpressionsBasedModel model, Variable[] lpVars, Problem problem) {
        this.model = model;
        this.lpVars = lpVars;
        this.problem = problem;
        this.cutGenerators = new ArrayList<>();
        this.variableIndexes = new HashMap<>();
        this.metadata = new HashMap<>();
        this.generatedCutCount = 0;
        for (int i = 0; i < lpVars.length; i++) {
            this.variableIndexes.put(lpVars[i], i);
        }
    }

    /**
     * Add a new named expression (constraint) to the LP model.
     *
     * @param name the name for the expression
     * @return the created expression
     */
    public Expression addExpression(String name) {
        return model.addExpression(name);
    }

    /**
     * Add a new LP variable to the model (e.g., for reification).
     *
     * @param var the variable to add
     */
    public void addVariable(Variable var) {
        model.addVariable(var);
        variableIndexes.putIfAbsent(var, variableIndexes.size());
    }

    /**
     * Get the LP variable corresponding to a CP variable.
     *
     * @param cpVar the CP variable
     * @return the corresponding LP variable
     */
    public Variable getLpVar(variables.Variable cpVar) {
        return lpVars[cpVar.num];
    }

    /**
     * Get the LP variable by index.
     *
     * @param index the variable index
     * @return the LP variable at that index
     */
    public Variable getLpVar(int index) {
        return lpVars[index];
    }

    public int getLpIndex(Variable lpVar) {
        Integer index = variableIndexes.get(lpVar);
        return index == null ? -1 : index.intValue();
    }

    /**
     * Check if a domain represents a binary {0,1} variable.
     *
     * @param dom the domain to check
     * @return true if domain is contained in {0,1}
     */
    public boolean isBinary01Domain(Domain dom) {
        return dom.firstValue() >= 0 && dom.lastValue() <= 1;
    }

    /**
     * Get the underlying problem.
     *
     * @return the CP problem
     */
    public Problem getProblem() {
        return problem;
    }

    /**
     * Increment and return the cover cut counter.
     * Used for generating unique names for knapsack cover cuts.
     *
     * @return the next cover cut number
     */
    public int nextGeneratedCutId() {
        return generatedCutCount++;
    }

    /**
     * Register a cut generator to be called after LP solves.
     *
     * @param generator the generator to register
     */
    public void registerCutGenerator(LpCutGenerator generator) {
        cutGenerators.add(generator);
    }

    @SuppressWarnings("unchecked")
    public <T> T getOrCreateMetadata(String key, Supplier<T> supplier) {
        return (T) metadata.computeIfAbsent(key, k -> supplier.get());
    }

    /**
     * Get the registered cut generators.
     *
     * @return the registered generators
     */
    public List<LpCutGenerator> getCutGenerators() {
        return List.copyOf(cutGenerators);
    }

    /**
     * Build a cut-generation context for the current LP solution.
     *
     * @param lpValues the current LP values
     * @return the cut-generation context
     */
    public CutGenerationContext cutGenerationContext(double[] lpValues) {
        return new CutGenerationContext(this, lpValues);
    }

    /**
     * Get the total number of generated cuts.
     *
     * @return the generated cut count
     */
    public int getGeneratedCutCount() {
        return generatedCutCount;
    }

    /**
     * Get the number of registered cut generators.
     *
     * @return the generator count
     */
    public int getCutGeneratorCount() {
        return cutGenerators.size();
    }
}
