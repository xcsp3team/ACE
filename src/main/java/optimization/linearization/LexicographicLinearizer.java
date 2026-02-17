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
import constraints.global.Lexicographic;
import constraints.global.Lexicographic.LexicographicLE;
import constraints.global.Lexicographic.LexicographicLT;
import constraints.global.Lexicographic.LexicographicCstL;
import constraints.global.Lexicographic.LexicographicCstG;
import variables.Variable;

/**
 * Linearizer for Lexicographic constraints.
 *
 * Handles both variable-variable and variable-constant versions:
 * - LexicographicLE/LT: list1 <=/<_lex list2
 * - LexicographicCstL: list <=/<_lex constant_tuple
 * - LexicographicCstG: list >=/>_lex constant_tuple
 *
 * Uses big-M formulation with auxiliary binary variables δ_i:
 * - δ_i = 1 means "strictly less has been established at or before position i"
 * - When δ_i = 0: x_i <= y_i (or x_i < y_i at position i)
 */
public class LexicographicLinearizer implements ConstraintLinearizer {

    @Override
    public boolean canLinearize(Constraint c) {
        return c instanceof LexicographicLE
            || c instanceof LexicographicLT
            || c instanceof LexicographicCstL
            || c instanceof LexicographicCstG;
    }

    @Override
    public boolean linearize(Constraint c, LinearizationContext ctx) {
        if (c instanceof LexicographicLE) {
            return addLexVar((Lexicographic.LexicographicVar) c, false, ctx);
        } else if (c instanceof LexicographicLT) {
            return addLexVar((Lexicographic.LexicographicVar) c, true, ctx);
        } else if (c instanceof LexicographicCstL) {
            return addLexCstL((LexicographicCstL) c, ctx);
        } else if (c instanceof LexicographicCstG) {
            return addLexCstG((LexicographicCstG) c, ctx);
        }
        return false;
    }

    /**
     * list1 <=/< _lex list2
     *
     * Big-M formulation:
     * - δ_i ∈ {0,1}: "strictly less established at or before position i"
     * - δ_0 = 0 (not yet established before first position)
     * - x_i - y_i ≤ M_i · δ_i (when δ_i=0, forces x_i ≤ y_i)
     * - δ_{i+1} ≥ δ_i (monotonic: once established, stays established)
     * - For strict (<): δ_{n-1} = 1 or x_{n-1} < y_{n-1}
     */
    private boolean addLexVar(Lexicographic.LexicographicVar ctr, boolean strict, LinearizationContext ctx) {
        Variable[] scp = ctr.scp;
        int half = scp.length / 2;

        if (half < 1) {
            return !strict; // Empty lists: <= satisfied, < not satisfied
        }

        // scp layout: [list1[0], list1[1], ..., list2[0], list2[1], ...]
        // Actually, looking at the code, scp is [list1..., list2...]
        // Let's extract the lists
        org.ojalgo.optimisation.Variable[] delta = new org.ojalgo.optimisation.Variable[half];

        // Create δ variables
        for (int i = 0; i < half; i++) {
            delta[i] = org.ojalgo.optimisation.Variable
                .make("lex_" + ctr.num + "_d" + i).lower(0).upper(1);
            ctx.addVariable(delta[i]);
        }

        // Constraints for each position
        for (int i = 0; i < half; i++) {
            Variable xi = scp[i];           // list1[i]
            Variable yi = scp[half + i];    // list2[i]

            // Compute big-M for this position
            double M = xi.dom.lastValue() - yi.dom.firstValue();
            if (M < 0) M = 0; // Already x <= y guaranteed

            // x_i - y_i ≤ M · δ_i
            Expression ub = ctx.addExpression("lex_ub_" + ctr.num + "_" + i);
            ub.set(ctx.getLpVar(xi), 1);
            ub.set(ctx.getLpVar(yi), -1);
            ub.set(delta[i], -M);
            ub.upper(0);

            // δ monotonicity: δ_{i+1} >= δ_i (for i < half-1)
            if (i < half - 1) {
                Expression mono = ctx.addExpression("lex_mono_" + ctr.num + "_" + i);
                mono.set(delta[i + 1], 1);
                mono.set(delta[i], -1);
                mono.lower(0);
            }
        }

        // For strict ordering: need at least one strict inequality
        // This is hard to model exactly in LP; we use a relaxation:
        // Either δ_{n-1} = 1 (already strictly less), or we need x_{n-1} < y_{n-1}
        // In LP relaxation, we just ensure the constraint can be satisfied
        if (strict) {
            // For strict, the last position must be decided: δ_{n-1} must eventually be 1
            // or x_{n-1} < y_{n-1}. This is naturally handled by the constraint being
            // propagated during search. For LP, we add no extra constraint (valid relaxation).
        }

        return true;
    }

    /**
     * list <=/< _lex limit (constant tuple)
     */
    private boolean addLexCstL(LexicographicCstL ctr, boolean strict, LinearizationContext ctx) {
        Variable[] list = ctr.scp;
        int n = list.length;

        if (n < 1) {
            return !strict;
        }

        // Use reflection to get the limit array
        int[] limit;
        try {
            java.lang.reflect.Field limitField = Lexicographic.LexicographicCst.class.getDeclaredField("limit");
            limitField.setAccessible(true);
            limit = (int[]) limitField.get(ctr);
        } catch (Exception e) {
            return false; // Can't access limit, skip linearization
        }

        org.ojalgo.optimisation.Variable[] delta = new org.ojalgo.optimisation.Variable[n];

        // Create δ variables
        for (int i = 0; i < n; i++) {
            delta[i] = org.ojalgo.optimisation.Variable
                .make("lexL_" + ctr.num + "_d" + i).lower(0).upper(1);
            ctx.addVariable(delta[i]);
        }

        // Constraints for each position: x_i - limit[i] ≤ M · δ_i
        for (int i = 0; i < n; i++) {
            Variable xi = list[i];
            double M = xi.dom.lastValue() - limit[i];
            if (M < 0) M = 0;

            Expression ub = ctx.addExpression("lexL_ub_" + ctr.num + "_" + i);
            ub.set(ctx.getLpVar(xi), 1);
            ub.set(delta[i], -M);
            ub.upper(limit[i]);

            if (i < n - 1) {
                Expression mono = ctx.addExpression("lexL_mono_" + ctr.num + "_" + i);
                mono.set(delta[i + 1], 1);
                mono.set(delta[i], -1);
                mono.lower(0);
            }
        }

        return true;
    }

    private boolean addLexCstL(LexicographicCstL ctr, LinearizationContext ctx) {
        // Check if strict ordering
        boolean strict;
        try {
            java.lang.reflect.Field strictField = Lexicographic.class.getDeclaredField("strictOrdering");
            strictField.setAccessible(true);
            strict = (boolean) strictField.get(ctr);
        } catch (Exception e) {
            strict = false;
        }
        return addLexCstL(ctr, strict, ctx);
    }

    /**
     * list >=/> _lex limit (constant tuple)
     * Equivalent to: limit <=/< _lex list
     */
    private boolean addLexCstG(LexicographicCstG ctr, boolean strict, LinearizationContext ctx) {
        Variable[] list = ctr.scp;
        int n = list.length;

        if (n < 1) {
            return !strict;
        }

        int[] limit;
        try {
            java.lang.reflect.Field limitField = Lexicographic.LexicographicCst.class.getDeclaredField("limit");
            limitField.setAccessible(true);
            limit = (int[]) limitField.get(ctr);
        } catch (Exception e) {
            return false;
        }

        org.ojalgo.optimisation.Variable[] delta = new org.ojalgo.optimisation.Variable[n];

        // Create δ variables
        for (int i = 0; i < n; i++) {
            delta[i] = org.ojalgo.optimisation.Variable
                .make("lexG_" + ctr.num + "_d" + i).lower(0).upper(1);
            ctx.addVariable(delta[i]);
        }

        // Constraints: limit[i] - x_i ≤ M · δ_i  =>  x_i >= limit[i] when δ_i = 0
        for (int i = 0; i < n; i++) {
            Variable xi = list[i];
            double M = limit[i] - xi.dom.firstValue();
            if (M < 0) M = 0;

            Expression lb = ctx.addExpression("lexG_lb_" + ctr.num + "_" + i);
            lb.set(ctx.getLpVar(xi), -1);
            lb.set(delta[i], -M);
            lb.upper(-limit[i]);

            if (i < n - 1) {
                Expression mono = ctx.addExpression("lexG_mono_" + ctr.num + "_" + i);
                mono.set(delta[i + 1], 1);
                mono.set(delta[i], -1);
                mono.lower(0);
            }
        }

        return true;
    }

    private boolean addLexCstG(LexicographicCstG ctr, LinearizationContext ctx) {
        boolean strict;
        try {
            java.lang.reflect.Field strictField = Lexicographic.class.getDeclaredField("strictOrdering");
            strictField.setAccessible(true);
            strict = (boolean) strictField.get(ctr);
        } catch (Exception e) {
            strict = false;
        }
        return addLexCstG(ctr, strict, ctx);
    }
}
