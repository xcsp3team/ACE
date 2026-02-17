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

import java.lang.reflect.Field;

import org.ojalgo.optimisation.Expression;

import constraints.Constraint;
import constraints.intension.Primitive2;
import constraints.intension.Reification;
import constraints.intension.Reification.Reif2.Reif2Rel.Reif2EQ;
import constraints.intension.Reification.Reif2.Reif2Rel.Reif2GE;
import constraints.intension.Reification.Reif2.Reif2Rel.Reif2LE;
import constraints.intension.Reification.Reif2.Reif2Rel.Reif2NE;
import constraints.intension.Reification.Reif3.Reif3GE;
import constraints.intension.Reification.Reif3.Reif3GT;
import constraints.intension.Reification.Reif3.Reif3LE;
import constraints.intension.Reification.Reif3.Reif3LT;
import constraints.intension.Reification.ReifLogic.ReifLogic2.LogEqAnd2;
import constraints.intension.Reification.ReifLogic.ReifLogic2.LogEqOr2;
import constraints.intension.Reification.ReifLogic.ReifLogicn.LogEqAnd;
import constraints.intension.Reification.ReifLogic.ReifLogicn.LogEqOr;
import variables.Variable;

/**
 * Linearizer for a subset of dedicated Reification constraints.
 *
 * Implemented families:
 * - Reif2LE / Reif2GE (exact big-M equivalence)
 * - Reif2EQ / Reif2NE (sound one-sided relaxations)
 * - Reif3LT / Reif3LE / Reif3GE / Reif3GT (exact big-M equivalence)
 * - LogEqAnd2 / LogEqOr2 / LogEqAnd / LogEqOr (exact boolean hulls)
 * - DisjonctiveReified (exact branch-selection big-M)
 */
public class ReificationLinearizer implements ConstraintLinearizer {

    @Override
    public boolean canLinearize(Constraint c) {
        return c instanceof Reif2LE
            || c instanceof Reif2GE
            || c instanceof Reif2EQ
            || c instanceof Reif2NE
            || c instanceof Reif3LT
            || c instanceof Reif3LE
            || c instanceof Reif3GE
            || c instanceof Reif3GT
            || c instanceof LogEqAnd2
            || c instanceof LogEqOr2
            || c instanceof LogEqAnd
            || c instanceof LogEqOr
            || c instanceof Reification.DisjonctiveReified;
    }

    @Override
    public boolean linearize(Constraint c, LinearizationContext ctx) {
        if (c instanceof Reif2LE) {
            return addReif2LE((Reif2LE) c, ctx);
        } else if (c instanceof Reif2GE) {
            return addReif2GE((Reif2GE) c, ctx);
        } else if (c instanceof Reif2EQ) {
            return addReif2EQ((Reif2EQ) c, ctx);
        } else if (c instanceof Reif2NE) {
            return addReif2NE((Reif2NE) c, ctx);
        } else if (c instanceof Reif3LT) {
            return addReif3LT((Reif3LT) c, ctx);
        } else if (c instanceof Reif3LE) {
            return addReif3LE((Reif3LE) c, ctx);
        } else if (c instanceof Reif3GE) {
            return addReif3GE((Reif3GE) c, ctx);
        } else if (c instanceof Reif3GT) {
            return addReif3GT((Reif3GT) c, ctx);
        } else if (c instanceof LogEqAnd2) {
            return addLogEqAnd2((LogEqAnd2) c, ctx);
        } else if (c instanceof LogEqOr2) {
            return addLogEqOr2((LogEqOr2) c, ctx);
        } else if (c instanceof LogEqAnd) {
            return addLogEqAnd((LogEqAnd) c, ctx);
        } else if (c instanceof LogEqOr) {
            return addLogEqOr((LogEqOr) c, ctx);
        } else if (c instanceof Reification.DisjonctiveReified) {
            return addDisjonctiveReified((Reification.DisjonctiveReified) c, ctx);
        }
        return false;
    }

    private boolean addReif2LE(Reif2LE ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        Integer k = extractPrimitiveK(ctr);
        if (k == null || !isBinary01(x, ctx)) {
            return false;
        }
        return addEquivLe(x, y, k, "reif2LE_" + ctr.num, ctx);
    }

    private boolean addReif2GE(Reif2GE ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        Integer k = extractPrimitiveK(ctr);
        if (k == null || !isBinary01(x, ctx)) {
            return false;
        }
        return addEquivGe(x, y, k, "reif2GE_" + ctr.num, ctx);
    }

    /**
     * Sound relaxation for x = (y == k):
     * x=1 => y=k is enforced; x=0 branch is relaxed.
     */
    private boolean addReif2EQ(Reif2EQ ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        Integer k = extractPrimitiveK(ctr);
        if (k == null || !isBinary01(x, ctx)) {
            return false;
        }

        double l = y.dom.firstValue();
        double u = y.dom.lastValue();
        double kk = k.doubleValue();

        // x = 1 => y <= k
        Expression ub = ctx.addExpression("reif2EQ_ub_" + ctr.num);
        ub.set(ctx.getLpVar(y), 1);
        ub.set(ctx.getLpVar(x), u - kk);
        ub.upper(u);

        // x = 1 => y >= k
        Expression lb = ctx.addExpression("reif2EQ_lb_" + ctr.num);
        lb.set(ctx.getLpVar(y), 1);
        lb.set(ctx.getLpVar(x), -(kk - l));
        lb.lower(l);

        return true;
    }

    /**
     * Sound relaxation for x = (y != k):
     * x=0 => y=k is enforced; x=1 branch is relaxed.
     */
    private boolean addReif2NE(Reif2NE ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        Integer k = extractPrimitiveK(ctr);
        if (k == null || !isBinary01(x, ctx)) {
            return false;
        }

        double l = y.dom.firstValue();
        double u = y.dom.lastValue();
        double kk = k.doubleValue();

        // x = 0 => y <= k
        Expression ub = ctx.addExpression("reif2NE_ub_" + ctr.num);
        ub.set(ctx.getLpVar(y), 1);
        ub.set(ctx.getLpVar(x), -(u - kk));
        ub.upper(kk);

        // x = 0 => y >= k
        Expression lb = ctx.addExpression("reif2NE_lb_" + ctr.num);
        lb.set(ctx.getLpVar(y), 1);
        lb.set(ctx.getLpVar(x), kk - l);
        lb.lower(kk);

        return true;
    }

    private boolean addReif3LT(Reif3LT ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0], y = ctr.scp[1], z = ctr.scp[2];
        if (!isBinary01(x, ctx)) {
            return false;
        }
        return addEquivDiffLe(x, y, z, -1.0, "reif3LT_" + ctr.num, ctx);
    }

    private boolean addReif3LE(Reif3LE ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0], y = ctr.scp[1], z = ctr.scp[2];
        if (!isBinary01(x, ctx)) {
            return false;
        }
        return addEquivDiffLe(x, y, z, 0.0, "reif3LE_" + ctr.num, ctx);
    }

    private boolean addReif3GE(Reif3GE ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0], y = ctr.scp[1], z = ctr.scp[2];
        if (!isBinary01(x, ctx)) {
            return false;
        }
        return addEquivDiffGe(x, y, z, 0.0, "reif3GE_" + ctr.num, ctx);
    }

    private boolean addReif3GT(Reif3GT ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0], y = ctr.scp[1], z = ctr.scp[2];
        if (!isBinary01(x, ctx)) {
            return false;
        }
        return addEquivDiffGe(x, y, z, 1.0, "reif3GT_" + ctr.num, ctx);
    }

    private boolean addLogEqAnd2(LogEqAnd2 ctr, LinearizationContext ctx) {
        Variable[] scp = ctr.scp; // [x, y, z]
        if (scp.length != 3 || !allBinary01(scp, ctx)) {
            return false;
        }
        Variable x = scp[0], y = scp[1], z = scp[2];

        // x <= y
        Expression c1 = ctx.addExpression("logAnd2_c1_" + ctr.num);
        c1.set(ctx.getLpVar(x), 1);
        c1.set(ctx.getLpVar(y), -1);
        c1.upper(0);

        // x <= z
        Expression c2 = ctx.addExpression("logAnd2_c2_" + ctr.num);
        c2.set(ctx.getLpVar(x), 1);
        c2.set(ctx.getLpVar(z), -1);
        c2.upper(0);

        // x >= y + z - 1  <=>  -x + y + z <= 1
        Expression c3 = ctx.addExpression("logAnd2_c3_" + ctr.num);
        c3.set(ctx.getLpVar(x), -1);
        c3.set(ctx.getLpVar(y), 1);
        c3.set(ctx.getLpVar(z), 1);
        c3.upper(1);

        return true;
    }

    private boolean addLogEqOr2(LogEqOr2 ctr, LinearizationContext ctx) {
        Variable[] scp = ctr.scp; // [x, y, z]
        if (scp.length != 3 || !allBinary01(scp, ctx)) {
            return false;
        }
        Variable x = scp[0], y = scp[1], z = scp[2];

        // x >= y
        Expression c1 = ctx.addExpression("logOr2_c1_" + ctr.num);
        c1.set(ctx.getLpVar(x), 1);
        c1.set(ctx.getLpVar(y), -1);
        c1.lower(0);

        // x >= z
        Expression c2 = ctx.addExpression("logOr2_c2_" + ctr.num);
        c2.set(ctx.getLpVar(x), 1);
        c2.set(ctx.getLpVar(z), -1);
        c2.lower(0);

        // x <= y + z  <=>  x - y - z <= 0
        Expression c3 = ctx.addExpression("logOr2_c3_" + ctr.num);
        c3.set(ctx.getLpVar(x), 1);
        c3.set(ctx.getLpVar(y), -1);
        c3.set(ctx.getLpVar(z), -1);
        c3.upper(0);

        return true;
    }

    private boolean addLogEqAnd(LogEqAnd ctr, LinearizationContext ctx) {
        Variable[] scp = ctr.scp; // [x, y1, ..., yn]
        if (scp.length < 3 || !allBinary01(scp, ctx)) {
            return false;
        }
        Variable x = scp[0];
        int n = scp.length - 1;

        // x <= yi for all i
        for (int i = 1; i < scp.length; i++) {
            Expression ub = ctx.addExpression("logAnd_c1_" + ctr.num + "_" + i);
            ub.set(ctx.getLpVar(x), 1);
            ub.set(ctx.getLpVar(scp[i]), -1);
            ub.upper(0);
        }

        // x >= sum(yi) - (n-1)  <=>  -x + sum(yi) <= n-1
        Expression lb = ctx.addExpression("logAnd_c2_" + ctr.num);
        lb.set(ctx.getLpVar(x), -1);
        for (int i = 1; i < scp.length; i++) {
            lb.set(ctx.getLpVar(scp[i]), 1);
        }
        lb.upper(n - 1);

        return true;
    }

    private boolean addLogEqOr(LogEqOr ctr, LinearizationContext ctx) {
        Variable[] scp = ctr.scp; // [x, y1, ..., yn]
        if (scp.length < 3 || !allBinary01(scp, ctx)) {
            return false;
        }
        Variable x = scp[0];

        // x >= yi for all i
        for (int i = 1; i < scp.length; i++) {
            Expression lb = ctx.addExpression("logOr_c1_" + ctr.num + "_" + i);
            lb.set(ctx.getLpVar(x), 1);
            lb.set(ctx.getLpVar(scp[i]), -1);
            lb.lower(0);
        }

        // x <= sum(yi)  <=>  x - sum(yi) <= 0
        Expression ub = ctx.addExpression("logOr_c2_" + ctr.num);
        ub.set(ctx.getLpVar(x), 1);
        for (int i = 1; i < scp.length; i++) {
            ub.set(ctx.getLpVar(scp[i]), -1);
        }
        ub.upper(0);

        return true;
    }

    private boolean addDisjonctiveReified(Reification.DisjonctiveReified ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        Variable z = ctr.scp[2];
        if (!isBinary01(z, ctx)) {
            return false;
        }

        Integer w1 = readIntField(ctr, Reification.DisjonctiveReified.class, "w1");
        Integer w2 = readIntField(ctr, Reification.DisjonctiveReified.class, "w2");
        if (w1 == null || w2 == null) {
            return false;
        }

        double m1 = Math.max(0.0, x.dom.lastValue() + w1 - y.dom.firstValue());
        double m2 = Math.max(0.0, y.dom.lastValue() + w2 - x.dom.firstValue());

        // z = 0 => x + w1 <= y
        // x + w1 <= y + M1*z  <=>  x - y - M1*z <= -w1
        Expression c1 = ctx.addExpression("disjReif_c1_" + ctr.num);
        c1.set(ctx.getLpVar(x), 1);
        c1.set(ctx.getLpVar(y), -1);
        c1.set(ctx.getLpVar(z), -m1);
        c1.upper(-w1);

        // z = 1 => y + w2 <= x
        // y + w2 <= x + M2*(1-z)  <=>  y - x + M2*z <= M2 - w2
        Expression c2 = ctx.addExpression("disjReif_c2_" + ctr.num);
        c2.set(ctx.getLpVar(y), 1);
        c2.set(ctx.getLpVar(x), -1);
        c2.set(ctx.getLpVar(z), m2);
        c2.upper(m2 - w2);

        return true;
    }

    /**
     * x <=> (y <= t)
     */
    private boolean addEquivLe(Variable x, Variable y, double t, String name, LinearizationContext ctx) {
        double l = y.dom.firstValue();
        double u = y.dom.lastValue();

        // y <= t + (u-t)*(1-x)  <=>  y + (u-t)*x <= u
        Expression ub = ctx.addExpression(name + "_ub");
        ub.set(ctx.getLpVar(y), 1);
        ub.set(ctx.getLpVar(x), u - t);
        ub.upper(u);

        // y >= t+1 - (t+1-l)*x  <=>  y + (t+1-l)*x >= t+1
        Expression lb = ctx.addExpression(name + "_lb");
        lb.set(ctx.getLpVar(y), 1);
        lb.set(ctx.getLpVar(x), t + 1 - l);
        lb.lower(t + 1);

        return true;
    }

    /**
     * x <=> (y >= t)
     */
    private boolean addEquivGe(Variable x, Variable y, double t, String name, LinearizationContext ctx) {
        double l = y.dom.firstValue();
        double u = y.dom.lastValue();

        // y >= t - (t-l)*(1-x)  <=>  y - (t-l)*x >= l
        Expression lb = ctx.addExpression(name + "_lb");
        lb.set(ctx.getLpVar(y), 1);
        lb.set(ctx.getLpVar(x), -(t - l));
        lb.lower(l);

        // y <= t-1 + (u-t+1)*x  <=>  y - (u-t+1)*x <= t-1
        Expression ub = ctx.addExpression(name + "_ub");
        ub.set(ctx.getLpVar(y), 1);
        ub.set(ctx.getLpVar(x), -(u - t + 1));
        ub.upper(t - 1);

        return true;
    }

    /**
     * x <=> ((y-z) <= t)
     */
    private boolean addEquivDiffLe(Variable x, Variable y, Variable z, double t, String name, LinearizationContext ctx) {
        double l = y.dom.firstValue() - z.dom.lastValue();
        double u = y.dom.lastValue() - z.dom.firstValue();

        // (y-z) <= t + (u-t)*(1-x)  <=>  (y-z) + (u-t)*x <= u
        Expression ub = ctx.addExpression(name + "_ub");
        ub.set(ctx.getLpVar(y), 1);
        ub.set(ctx.getLpVar(z), -1);
        ub.set(ctx.getLpVar(x), u - t);
        ub.upper(u);

        // (y-z) >= t+1 - (t+1-l)*x  <=>  (y-z) + (t+1-l)*x >= t+1
        Expression lb = ctx.addExpression(name + "_lb");
        lb.set(ctx.getLpVar(y), 1);
        lb.set(ctx.getLpVar(z), -1);
        lb.set(ctx.getLpVar(x), t + 1 - l);
        lb.lower(t + 1);

        return true;
    }

    /**
     * x <=> ((y-z) >= t)
     */
    private boolean addEquivDiffGe(Variable x, Variable y, Variable z, double t, String name, LinearizationContext ctx) {
        double l = y.dom.firstValue() - z.dom.lastValue();
        double u = y.dom.lastValue() - z.dom.firstValue();

        // (y-z) >= t - (t-l)*(1-x)  <=>  (y-z) - (t-l)*x >= l
        Expression lb = ctx.addExpression(name + "_lb");
        lb.set(ctx.getLpVar(y), 1);
        lb.set(ctx.getLpVar(z), -1);
        lb.set(ctx.getLpVar(x), -(t - l));
        lb.lower(l);

        // (y-z) <= t-1 + (u-t+1)*x  <=>  (y-z) - (u-t+1)*x <= t-1
        Expression ub = ctx.addExpression(name + "_ub");
        ub.set(ctx.getLpVar(y), 1);
        ub.set(ctx.getLpVar(z), -1);
        ub.set(ctx.getLpVar(x), -(u - t + 1));
        ub.upper(t - 1);

        return true;
    }

    private boolean allBinary01(Variable[] vars, LinearizationContext ctx) {
        for (Variable v : vars) {
            if (!isBinary01(v, ctx)) {
                return false;
            }
        }
        return true;
    }

    private boolean isBinary01(Variable x, LinearizationContext ctx) {
        return ctx.isBinary01Domain(x.dom);
    }

    private Integer extractPrimitiveK(Constraint ctr) {
        return readIntField(ctr, Primitive2.class, "k");
    }

    private Integer readIntField(Object target, Class<?> owner, String fieldName) {
        try {
            Field f = owner.getDeclaredField(fieldName);
            f.setAccessible(true);
            return (Integer) f.get(target);
        } catch (Exception e) {
            return null;
        }
    }
}
