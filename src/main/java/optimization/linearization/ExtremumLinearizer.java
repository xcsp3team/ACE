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
import constraints.global.Extremum.ExtremumCst.MaximumCst;
import constraints.global.Extremum.ExtremumCst.MinimumCst;
import constraints.global.Extremum.ExtremumVar;
import variables.Variable;

/**
 * Linearizer for Extremum constraints (Minimum and Maximum).
 *
 * Handles constant-limit variants:
 * - MinimumCstGE: min(x_i) >= k  →  x_i >= k for all i (exact)
 * - MinimumCstLE: min(x_i) <= k  →  relaxed (at least one x_i <= k, needs big-M)
 * - MaximumCstLE: max(x_i) <= k  →  x_i <= k for all i (exact)
 * - MaximumCstGE: max(x_i) >= k  →  relaxed (at least one x_i >= k, needs big-M)
 *
 * Handles variable-result variants:
 * - Maximum: y = max(x_i)  →  y >= x_i for all i (valid relaxation)
 * - Minimum: y = min(x_i)  →  y <= x_i for all i (valid relaxation)
 */
public class ExtremumLinearizer implements ConstraintLinearizer {

    @Override
    public boolean canLinearize(Constraint c) {
        return c instanceof MinimumCst.MinimumCstGE
            || c instanceof MinimumCst.MinimumCstLE
            || c instanceof MinimumCst.MinimumCstEQ
            || c instanceof MaximumCst.MaximumCstLE
            || c instanceof MaximumCst.MaximumCstGE
            || c instanceof MaximumCst.MaximumCstEQ
            || c instanceof ExtremumVar.Maximum
            || c instanceof ExtremumVar.Minimum;
    }

    @Override
    public boolean linearize(Constraint c, LinearizationContext ctx) {
        if (c instanceof MinimumCst.MinimumCstGE) {
            return addMinimumCstGE((MinimumCst) c, ctx);
        } else if (c instanceof MinimumCst.MinimumCstLE) {
            return addMinimumCstLE((MinimumCst) c, ctx);
        } else if (c instanceof MinimumCst.MinimumCstEQ) {
            return addMinimumCstEQ((MinimumCst) c, ctx);
        } else if (c instanceof MaximumCst.MaximumCstLE) {
            return addMaximumCstLE((MaximumCst) c, ctx);
        } else if (c instanceof MaximumCst.MaximumCstGE) {
            return addMaximumCstGE((MaximumCst) c, ctx);
        } else if (c instanceof MaximumCst.MaximumCstEQ) {
            return addMaximumCstEQ((MaximumCst) c, ctx);
        } else if (c instanceof ExtremumVar.Maximum) {
            return addMaximumVar((ExtremumVar.Maximum) c, ctx);
        } else if (c instanceof ExtremumVar.Minimum) {
            return addMinimumVar((ExtremumVar.Minimum) c, ctx);
        }
        return false;
    }

    /**
     * min(x_i) >= k  →  x_i >= k for all i
     * This is an exact linearization.
     */
    private boolean addMinimumCstGE(MinimumCst ctr, LinearizationContext ctx) {
        long limit = ctr.limit();
        for (Variable var : ctr.scp) {
            Expression expr = ctx.addExpression("minGE_" + ctr.num + "_" + var.num);
            expr.set(ctx.getLpVar(var), 1);
            expr.lower(limit);
        }
        return true;
    }

    /**
     * min(x_i) <= k  →  at least one x_i <= k
     * Uses big-M formulation with auxiliary binaries.
     */
    private boolean addMinimumCstLE(MinimumCst ctr, LinearizationContext ctx) {
        long limit = ctr.limit();
        Variable[] list = ctr.scp;

        // sum(b_i) >= 1: at least one variable witnesses min <= k
        Expression atLeastOne = ctx.addExpression("minLE_witness_" + ctr.num);

        for (int i = 0; i < list.length; i++) {
            Variable var = list[i];
            double M = var.dom.lastValue() - limit;
            if (M <= 0) {
                // Variable already satisfies x_i <= k, trivially true
                return true;
            }

            // Create auxiliary binary b_i
            org.ojalgo.optimisation.Variable bi = org.ojalgo.optimisation.Variable
                .make("minLE_" + ctr.num + "_b" + i).lower(0).upper(1);
            ctx.addVariable(bi);

            // b_i = 1 => x_i <= k: x_i <= k + M*(1-b_i) => x_i + M*b_i <= k + M
            Expression impl = ctx.addExpression("minLE_impl_" + ctr.num + "_" + i);
            impl.set(ctx.getLpVar(var), 1);
            impl.set(bi, M);
            impl.upper(limit + M);

            atLeastOne.set(bi, 1);
        }
        atLeastOne.lower(1);
        return true;
    }

    /**
     * min(x_i) = k  →  (min >= k) AND (min <= k)
     */
    private boolean addMinimumCstEQ(MinimumCst ctr, LinearizationContext ctx) {
        // Combine both directions
        addMinimumCstGE(ctr, ctx);
        addMinimumCstLE(ctr, ctx);
        return true;
    }

    /**
     * max(x_i) <= k  →  x_i <= k for all i
     * This is an exact linearization.
     */
    private boolean addMaximumCstLE(MaximumCst ctr, LinearizationContext ctx) {
        long limit = ctr.limit();
        for (Variable var : ctr.scp) {
            Expression expr = ctx.addExpression("maxLE_" + ctr.num + "_" + var.num);
            expr.set(ctx.getLpVar(var), 1);
            expr.upper(limit);
        }
        return true;
    }

    /**
     * max(x_i) >= k  →  at least one x_i >= k
     * Uses big-M formulation with auxiliary binaries.
     */
    private boolean addMaximumCstGE(MaximumCst ctr, LinearizationContext ctx) {
        long limit = ctr.limit();
        Variable[] list = ctr.scp;

        // sum(b_i) >= 1: at least one variable witnesses max >= k
        Expression atLeastOne = ctx.addExpression("maxGE_witness_" + ctr.num);

        for (int i = 0; i < list.length; i++) {
            Variable var = list[i];
            double M = limit - var.dom.firstValue();
            if (M <= 0) {
                // Variable already satisfies x_i >= k, trivially true
                return true;
            }

            // Create auxiliary binary b_i
            org.ojalgo.optimisation.Variable bi = org.ojalgo.optimisation.Variable
                .make("maxGE_" + ctr.num + "_b" + i).lower(0).upper(1);
            ctx.addVariable(bi);

            // b_i = 1 => x_i >= k: x_i >= k - M*(1-b_i) => x_i - M*b_i >= k - M
            Expression impl = ctx.addExpression("maxGE_impl_" + ctr.num + "_" + i);
            impl.set(ctx.getLpVar(var), 1);
            impl.set(bi, -M);
            impl.lower(limit - M);

            atLeastOne.set(bi, 1);
        }
        atLeastOne.lower(1);
        return true;
    }

    /**
     * max(x_i) = k  →  (max <= k) AND (max >= k)
     */
    private boolean addMaximumCstEQ(MaximumCst ctr, LinearizationContext ctx) {
        // Combine both directions
        addMaximumCstLE(ctr, ctx);
        addMaximumCstGE(ctr, ctx);
        return true;
    }

    /**
     * y = max(x_i)  →  y >= x_i for all i
     * This is a valid LP relaxation (y may exceed true max).
     */
    private boolean addMaximumVar(ExtremumVar.Maximum ctr, LinearizationContext ctx) {
        // scp[0] is the result variable y, scp[1..n] are the list variables
        Variable y = ctr.scp[0];
        for (int i = 1; i < ctr.scp.length; i++) {
            Variable xi = ctr.scp[i];
            // y >= x_i  =>  y - x_i >= 0
            Expression expr = ctx.addExpression("max_lb_" + ctr.num + "_" + i);
            expr.set(ctx.getLpVar(y), 1);
            expr.set(ctx.getLpVar(xi), -1);
            expr.lower(0);
        }
        return true;
    }

    /**
     * y = min(x_i)  →  y <= x_i for all i
     * This is a valid LP relaxation (y may be below true min).
     */
    private boolean addMinimumVar(ExtremumVar.Minimum ctr, LinearizationContext ctx) {
        // scp[0] is the result variable y, scp[1..n] are the list variables
        Variable y = ctr.scp[0];
        for (int i = 1; i < ctr.scp.length; i++) {
            Variable xi = ctr.scp[i];
            // y <= x_i  =>  y - x_i <= 0
            Expression expr = ctx.addExpression("min_ub_" + ctr.num + "_" + i);
            expr.set(ctx.getLpVar(y), 1);
            expr.set(ctx.getLpVar(xi), -1);
            expr.upper(0);
        }
        return true;
    }
}
