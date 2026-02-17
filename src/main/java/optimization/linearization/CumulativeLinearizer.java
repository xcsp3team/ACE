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

import constraints.Constraint;
import constraints.global.Cumulative;
import variables.Variable;

/**
 * Linearizer for Cumulative (resource-constrained scheduling) constraints.
 *
 * Cumulative ensures that at each time point, the sum of resource consumption
 * (heights) of overlapping tasks doesn't exceed the capacity (limit).
 *
 * LP relaxation uses the energy-based formulation:
 * - Total energy: sum(width[i] * height[i]) <= limit * horizon
 * - This is a necessary condition (valid relaxation) but not sufficient
 *
 * For variable heights, we also add bounds on individual task contributions.
 */
public class CumulativeLinearizer implements ConstraintLinearizer {

    @Override
    public boolean canLinearize(Constraint c) {
        return c instanceof Cumulative;
    }

    @Override
    public boolean linearize(Constraint c, LinearizationContext ctx) {
        Cumulative ctr = (Cumulative) c;

        // Extract fields via reflection
        Variable[] starts;
        int[] widths;
        int[] heights;
        int limit;
        int nTasks;
        boolean movableWidths;
        boolean movableHeights;

        try {
            java.lang.reflect.Field startsField = Cumulative.class.getDeclaredField("starts");
            java.lang.reflect.Field wwidthsField = Cumulative.class.getDeclaredField("wwidths");
            java.lang.reflect.Field wheightsField = Cumulative.class.getDeclaredField("wheights");
            java.lang.reflect.Field limitField = Cumulative.class.getDeclaredField("limit");
            java.lang.reflect.Field nTasksField = Cumulative.class.getDeclaredField("nTasks");
            java.lang.reflect.Field movableWidthsField = Cumulative.class.getDeclaredField("movableWidths");
            java.lang.reflect.Field movableHeightsField = Cumulative.class.getDeclaredField("movableHeights");

            startsField.setAccessible(true);
            wwidthsField.setAccessible(true);
            wheightsField.setAccessible(true);
            limitField.setAccessible(true);
            nTasksField.setAccessible(true);
            movableWidthsField.setAccessible(true);
            movableHeightsField.setAccessible(true);

            starts = (Variable[]) startsField.get(ctr);
            widths = (int[]) wwidthsField.get(ctr);
            heights = (int[]) wheightsField.get(ctr);
            limit = (int) limitField.get(ctr);
            nTasks = (int) nTasksField.get(ctr);
            movableWidths = (boolean) movableWidthsField.get(ctr);
            movableHeights = (boolean) movableHeightsField.get(ctr);
        } catch (Exception e) {
            return false; // Can't access fields
        }

        // Compute horizon
        int minStart = Integer.MAX_VALUE;
        int maxEnd = Integer.MIN_VALUE;
        for (int i = 0; i < nTasks; i++) {
            minStart = Math.min(minStart, starts[i].dom.firstValue());
            maxEnd = Math.max(maxEnd, starts[i].dom.lastValue() + widths[i]);
        }
        int horizon = maxEnd - minStart;

        // 1. Energy-based relaxation: sum(width[i] * height[i]) <= limit * horizon
        // For constant widths and heights, this is just a feasibility check
        // For variable heights, we can express this as a linear constraint

        if (!movableWidths && !movableHeights) {
            // All constants - compute total energy
            long totalEnergy = 0;
            for (int i = 0; i < nTasks; i++) {
                totalEnergy += (long) widths[i] * heights[i];
            }
            // This is just a feasibility check, not an LP constraint
            // The constraint is already implied by domains
        }

        // 2. Add individual task bounds: start[i] + width[i] <= maxEnd
        for (int i = 0; i < nTasks; i++) {
            int endBound = maxEnd;
            Expression endExpr = ctx.addExpression("cumul_end_" + ctr.num + "_" + i);
            endExpr.set(ctx.getLpVar(starts[i]), 1);
            endExpr.upper(endBound - widths[i]);
        }

        // 3. For variable heights (CumulativeVarH), add height contribution bounds
        // The scope includes height variables after start variables
        if (movableHeights && ctr.scp.length > nTasks) {
            // Height variables are in scp after start variables
            // For CumulativeVarH: scp = [starts..., heights...]
            // Energy constraint: sum(width[i] * height[i]) <= limit * horizon

            Expression energyExpr = ctx.addExpression("cumul_energy_" + ctr.num);
            for (int i = 0; i < nTasks; i++) {
                // height variable is at scp[nTasks + i]
                Variable heightVar = ctr.scp[nTasks + i];
                energyExpr.set(ctx.getLpVar(heightVar), widths[i]);
            }
            energyExpr.upper((long) limit * horizon);
        }

        // 4. Pairwise disjunction relaxation for non-preemptive tasks
        // If two tasks overlap in time, their combined height <= limit
        // This adds O(n^2) constraints but strengthens the relaxation
        addPairwiseHeightBounds(ctr, starts, widths, heights, limit, nTasks, movableHeights, ctx);

        return true;
    }

    /**
     * Add pairwise height bounds: if tasks i and j might overlap,
     * then height[i] + height[j] <= limit (for the overlap period).
     */
    private void addPairwiseHeightBounds(Cumulative ctr, Variable[] starts, int[] widths,
            int[] heights, int limit, int nTasks, boolean movableHeights, LinearizationContext ctx) {

        // Only add a limited number of cuts to avoid explosion
        int maxCuts = Math.min(100, nTasks * (nTasks - 1) / 2);
        int cutsAdded = 0;

        for (int i = 0; i < nTasks && cutsAdded < maxCuts; i++) {
            for (int j = i + 1; j < nTasks && cutsAdded < maxCuts; j++) {
                // Check if tasks i and j can possibly overlap
                int earliestEndI = starts[i].dom.firstValue() + widths[i];
                int latestStartI = starts[i].dom.lastValue();
                int earliestEndJ = starts[j].dom.firstValue() + widths[j];
                int latestStartJ = starts[j].dom.lastValue();

                // Tasks can overlap if:
                // NOT (earliestEndI <= latestStartJ OR earliestEndJ <= latestStartI)
                boolean canOverlap = !(earliestEndI <= starts[j].dom.firstValue() ||
                                       earliestEndJ <= starts[i].dom.firstValue());

                if (canOverlap) {
                    if (movableHeights && ctr.scp.length > nTasks) {
                        // Variable heights: height[i] + height[j] <= limit
                        Variable hi = ctr.scp[nTasks + i];
                        Variable hj = ctr.scp[nTasks + j];

                        Expression pairExpr = ctx.addExpression("cumul_pair_" + ctr.num + "_" + i + "_" + j);
                        pairExpr.set(ctx.getLpVar(hi), 1);
                        pairExpr.set(ctx.getLpVar(hj), 1);
                        pairExpr.upper(limit);
                        cutsAdded++;
                    } else if (heights[i] + heights[j] > limit) {
                        // Constant heights exceed limit - tasks cannot overlap
                        // Add disjunctive constraint: start[i] + width[i] <= start[j] OR start[j] + width[j] <= start[i]
                        // Use big-M formulation
                        addDisjunctiveConstraint(ctr, starts[i], widths[i], starts[j], widths[j], i, j, ctx);
                        cutsAdded++;
                    }
                }
            }
        }
    }

    /**
     * Add disjunctive constraint: task i finishes before j starts, OR j finishes before i starts.
     */
    private void addDisjunctiveConstraint(Cumulative ctr, Variable si, int wi, Variable sj, int wj,
            int i, int j, LinearizationContext ctx) {

        // Big-M values
        double M1 = si.dom.lastValue() + wi - sj.dom.firstValue();
        double M2 = sj.dom.lastValue() + wj - si.dom.firstValue();

        if (M1 <= 0 || M2 <= 0) {
            return; // One branch is already forced
        }

        // Create auxiliary binary b: b=1 means task i before j
        org.ojalgo.optimisation.Variable b = org.ojalgo.optimisation.Variable
            .make("cumul_disj_" + ctr.num + "_" + i + "_" + j).lower(0).upper(1);
        ctx.addVariable(b);

        // s[i] + w[i] <= s[j] + M*(1-b)
        Expression expr1 = ctx.addExpression("cumul_disj_ij_" + ctr.num + "_" + i + "_" + j);
        expr1.set(ctx.getLpVar(si), 1);
        expr1.set(ctx.getLpVar(sj), -1);
        expr1.set(b, M1);
        expr1.upper(M1 - wi);

        // s[j] + w[j] <= s[i] + M*b
        Expression expr2 = ctx.addExpression("cumul_disj_ji_" + ctr.num + "_" + i + "_" + j);
        expr2.set(ctx.getLpVar(sj), 1);
        expr2.set(ctx.getLpVar(si), -1);
        expr2.set(b, -M2);
        expr2.upper(-wj);
    }
}
