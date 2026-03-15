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
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import org.ojalgo.optimisation.Expression;

import constraints.Constraint;
import constraints.intension.Primitive2;
import constraints.intension.Primitive2.PrimitiveBinaryNoCst.*;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Add2.*;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Sub2.*;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Dist2.*;
import constraints.intension.Primitive2.PrimitiveBinaryVariant2.Dist2b.Dist2bEQ;
import variables.Variable;

/**
 * Linearizer for binary Primitive (Intension) constraints.
 *
 * Many Intension constraints are inherently linear:
 * - Add2: x + y op k
 * - Sub2: x - y op k
 * - Neg2EQ: x = -y (i.e., x + y = 0)
 * - Or2: x OR y for binary variables (x + y >= 1)
 * - Dist2: |x - y| op k (split into two linear constraints)
 *
 * This linearizer captures these cases for an exact or near-exact LP relaxation.
 */
public class PrimitiveLinearizer implements ConstraintLinearizer {

    private static final String DISJUNCTIVE_REGISTRY_KEY = PrimitiveLinearizer.class.getName() + ".disjunctiveRegistry";
    private static final double CUT_VIOLATION_EPS = 1e-6;
    private static final int MAX_NO_OVERLAP_CUTS_PER_ROUND = 10;

    private static final class TaskKey {
        final int variableNum;
        final int width;

        TaskKey(int variableNum, int width) {
            this.variableNum = variableNum;
            this.width = width;
        }

        static final Comparator<TaskKey> COMPARATOR = Comparator
                .comparingInt((TaskKey t) -> t.variableNum)
                .thenComparingInt(t -> t.width);

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (!(obj instanceof TaskKey))
                return false;
            TaskKey other = (TaskKey) obj;
            return variableNum == other.variableNum && width == other.width;
        }

        @Override
        public int hashCode() {
            return Objects.hash(variableNum, width);
        }

        @Override
        public String toString() {
            return variableNum + ":" + width;
        }
    }

    private static final class PairKey {
        final TaskKey first;
        final TaskKey second;

        PairKey(TaskKey a, TaskKey b) {
            if (TaskKey.COMPARATOR.compare(a, b) <= 0) {
                this.first = a;
                this.second = b;
            } else {
                this.first = b;
                this.second = a;
            }
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (!(obj instanceof PairKey))
                return false;
            PairKey other = (PairKey) obj;
            return first.equals(other.first) && second.equals(other.second);
        }

        @Override
        public int hashCode() {
            return Objects.hash(first, second);
        }
    }

    private static final class PairPrecedence {
        final org.ojalgo.optimisation.Variable selector;
        final boolean selectorMeansFirstBeforeSecond;

        PairPrecedence(org.ojalgo.optimisation.Variable selector, boolean selectorMeansFirstBeforeSecond) {
            this.selector = selector;
            this.selectorMeansFirstBeforeSecond = selectorMeansFirstBeforeSecond;
        }
    }

    private static final class DisjunctiveRegistry {
        final Map<TaskKey, Variable> startVars = new HashMap<>();
        final Map<PairKey, PairPrecedence> pairs = new HashMap<>();
        final List<TaskKey> tasks = new ArrayList<>();

        void add(TaskKey left, Variable leftVar, TaskKey right, Variable rightVar, org.ojalgo.optimisation.Variable selector) {
            startVars.putIfAbsent(left, leftVar);
            startVars.putIfAbsent(right, rightVar);
            if (!startVars.containsKey(left) || !startVars.containsKey(right))
                return;
            if (!tasks.contains(left))
                tasks.add(left);
            if (!tasks.contains(right))
                tasks.add(right);

            PairKey key = new PairKey(left, right);
            if (pairs.containsKey(key))
                return;
            boolean selectorMeansFirstBeforeSecond = key.first.equals(left);
            pairs.put(key, new PairPrecedence(selector, selectorMeansFirstBeforeSecond));
        }

        boolean hasPrecedence(TaskKey from, TaskKey to) {
            return pairs.containsKey(new PairKey(from, to));
        }

        double precedenceLpValue(TaskKey from, TaskKey to, CutGenerationContext ctx) {
            PairPrecedence precedence = pairs.get(new PairKey(from, to));
            if (precedence == null)
                return Double.NaN;
            double value = ctx.getLpValue(precedence.selector);
            boolean forward = new PairKey(from, to).first.equals(from);
            if (forward == precedence.selectorMeansFirstBeforeSecond)
                return value;
            return 1d - value;
        }

        double addPrecedenceTerm(Expression cut, TaskKey from, TaskKey to, CutGenerationContext ctx) {
            PairPrecedence precedence = pairs.get(new PairKey(from, to));
            if (precedence == null)
                return 0d;
            boolean forward = new PairKey(from, to).first.equals(from);
            if (forward == precedence.selectorMeansFirstBeforeSecond) {
                cut.set(precedence.selector, 1);
                return 0d;
            }
            cut.set(precedence.selector, -1);
            return 1d;
        }
    }

    private static final class NoOverlapTriangleCutGenerator implements LpCutGenerator {
        private final DisjunctiveRegistry registry;
        private final Set<String> emittedCuts = new HashSet<>();

        NoOverlapTriangleCutGenerator(DisjunctiveRegistry registry) {
            this.registry = registry;
        }

        @Override
        public String name() {
            return "NoOverlapTriangle";
        }

        @Override
        public int generateCuts(CutGenerationContext ctx) {
            int cuts = 0;
            List<TaskKey> tasks = new ArrayList<>(registry.tasks);
            tasks.sort(TaskKey.COMPARATOR);

            for (int i = 0; i < tasks.size() && cuts < MAX_NO_OVERLAP_CUTS_PER_ROUND; i++) {
                TaskKey a = tasks.get(i);
                for (int j = i + 1; j < tasks.size() && cuts < MAX_NO_OVERLAP_CUTS_PER_ROUND; j++) {
                    TaskKey b = tasks.get(j);
                    if (a.variableNum == b.variableNum)
                        continue;
                    for (int k = j + 1; k < tasks.size() && cuts < MAX_NO_OVERLAP_CUTS_PER_ROUND; k++) {
                        TaskKey c = tasks.get(k);
                        if (a.variableNum == c.variableNum || b.variableNum == c.variableNum)
                            continue;
                        if (!registry.hasPrecedence(a, b) || !registry.hasPrecedence(b, c) || !registry.hasPrecedence(c, a))
                            continue;

                        cuts += tryAddCycleCut(a, b, c, ctx);
                        if (cuts >= MAX_NO_OVERLAP_CUTS_PER_ROUND)
                            break;
                        cuts += tryAddCycleCut(a, c, b, ctx);
                    }
                }
            }
            return cuts;
        }

        private int tryAddCycleCut(TaskKey first, TaskKey second, TaskKey third, CutGenerationContext ctx) {
            double lhs = registry.precedenceLpValue(first, second, ctx)
                    + registry.precedenceLpValue(second, third, ctx)
                    + registry.precedenceLpValue(third, first, ctx);
            if (lhs <= 2d + CUT_VIOLATION_EPS)
                return 0;

            String signature = cycleSignature(first, second, third);
            if (!emittedCuts.add(signature))
                return 0;

            Expression cut = ctx.addExpression("noov_tri_" + ctx.nextGeneratedCutId());
            double constant = 0d;
            constant += registry.addPrecedenceTerm(cut, first, second, ctx);
            constant += registry.addPrecedenceTerm(cut, second, third, ctx);
            constant += registry.addPrecedenceTerm(cut, third, first, ctx);
            cut.upper(2d - constant);
            return 1;
        }

        private String cycleSignature(TaskKey first, TaskKey second, TaskKey third) {
            TaskKey[] ordered = new TaskKey[] { first, second, third };
            int best = 0;
            for (int i = 1; i < 3; i++) {
                if (TaskKey.COMPARATOR.compare(ordered[i], ordered[best]) < 0)
                    best = i;
            }
            TaskKey a = ordered[best];
            TaskKey b = ordered[(best + 1) % 3];
            TaskKey c = ordered[(best + 2) % 3];
            return a + ">" + b + ">" + c;
        }
    }

    @Override
    public boolean canLinearize(Constraint c) {
        return c instanceof Add2LE
            || c instanceof Add2GE
            || c instanceof Add2EQ
            || c instanceof Sub2LE
            || c instanceof Sub2GE
            || c instanceof Sub2EQ
            || c instanceof Neg2EQ
            || c instanceof Or2
            || c instanceof Dist2LE
            || c instanceof Dist2GE
            || c instanceof Dist2EQ
            || c instanceof Dist2bEQ
            || c instanceof Disjonctive;
    }

    @Override
    public boolean linearize(Constraint c, LinearizationContext ctx) {
        if (c instanceof Add2LE) {
            return addAdd2LE((Primitive2) c, ctx);
        } else if (c instanceof Add2GE) {
            return addAdd2GE((Primitive2) c, ctx);
        } else if (c instanceof Add2EQ) {
            return addAdd2EQ((Primitive2) c, ctx);
        } else if (c instanceof Sub2LE) {
            return addSub2LE((Primitive2) c, ctx);
        } else if (c instanceof Sub2GE) {
            return addSub2GE((Primitive2) c, ctx);
        } else if (c instanceof Sub2EQ) {
            return addSub2EQ((Primitive2) c, ctx);
        } else if (c instanceof Neg2EQ) {
            return addNeg2EQ((Primitive2) c, ctx);
        } else if (c instanceof Or2) {
            return addOr2((Primitive2) c, ctx);
        } else if (c instanceof Dist2LE) {
            return addDist2LE((Primitive2) c, ctx);
        } else if (c instanceof Dist2GE) {
            return addDist2GE((Primitive2) c, ctx);
        } else if (c instanceof Dist2EQ) {
            return addDist2EQ((Primitive2) c, ctx);
        } else if (c instanceof Dist2bEQ) {
            return addDist2bEQ((Primitive2) c, ctx);
        } else if (c instanceof Disjonctive) {
            return addDisjonctive((Disjonctive) c, ctx);
        }
        return false;
    }

    // Helper to get k from Primitive2 via reflection
    private int getK(Primitive2 p) {
        try {
            java.lang.reflect.Field kField = Primitive2.class.getDeclaredField("k");
            kField.setAccessible(true);
            return (int) kField.get(p);
        } catch (Exception e) {
            return 0;
        }
    }

    /**
     * x + y <= k
     */
    private boolean addAdd2LE(Primitive2 ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        int k = getK(ctr);

        Expression expr = ctx.addExpression("add2LE_" + ctr.num);
        expr.set(ctx.getLpVar(x), 1);
        expr.set(ctx.getLpVar(y), 1);
        expr.upper(k);
        return true;
    }

    /**
     * x + y >= k
     */
    private boolean addAdd2GE(Primitive2 ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        int k = getK(ctr);

        Expression expr = ctx.addExpression("add2GE_" + ctr.num);
        expr.set(ctx.getLpVar(x), 1);
        expr.set(ctx.getLpVar(y), 1);
        expr.lower(k);
        return true;
    }

    /**
     * x + y = k
     */
    private boolean addAdd2EQ(Primitive2 ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        int k = getK(ctr);

        Expression expr = ctx.addExpression("add2EQ_" + ctr.num);
        expr.set(ctx.getLpVar(x), 1);
        expr.set(ctx.getLpVar(y), 1);
        expr.level(k);
        return true;
    }

    /**
     * x - y <= k
     */
    private boolean addSub2LE(Primitive2 ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        int k = getK(ctr);

        Expression expr = ctx.addExpression("sub2LE_" + ctr.num);
        expr.set(ctx.getLpVar(x), 1);
        expr.set(ctx.getLpVar(y), -1);
        expr.upper(k);
        return true;
    }

    /**
     * x - y >= k
     */
    private boolean addSub2GE(Primitive2 ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        int k = getK(ctr);

        Expression expr = ctx.addExpression("sub2GE_" + ctr.num);
        expr.set(ctx.getLpVar(x), 1);
        expr.set(ctx.getLpVar(y), -1);
        expr.lower(k);
        return true;
    }

    /**
     * x - y = k
     */
    private boolean addSub2EQ(Primitive2 ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        int k = getK(ctr);

        Expression expr = ctx.addExpression("sub2EQ_" + ctr.num);
        expr.set(ctx.getLpVar(x), 1);
        expr.set(ctx.getLpVar(y), -1);
        expr.level(k);
        return true;
    }

    /**
     * x = -y  =>  x + y = 0
     */
    private boolean addNeg2EQ(Primitive2 ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];

        Expression expr = ctx.addExpression("neg2EQ_" + ctr.num);
        expr.set(ctx.getLpVar(x), 1);
        expr.set(ctx.getLpVar(y), 1);
        expr.level(0);
        return true;
    }

    /**
     * x OR y (binary 0/1 variables)  =>  x + y >= 1
     */
    private boolean addOr2(Primitive2 ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];

        Expression expr = ctx.addExpression("or2_" + ctr.num);
        expr.set(ctx.getLpVar(x), 1);
        expr.set(ctx.getLpVar(y), 1);
        expr.lower(1);
        return true;
    }

    /**
     * |x - y| <= k  =>  -k <= x - y <= k
     * Split into: x - y <= k AND y - x <= k
     */
    private boolean addDist2LE(Primitive2 ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        int k = getK(ctr);

        // x - y <= k
        Expression expr1 = ctx.addExpression("dist2LE_pos_" + ctr.num);
        expr1.set(ctx.getLpVar(x), 1);
        expr1.set(ctx.getLpVar(y), -1);
        expr1.upper(k);

        // y - x <= k  =>  x - y >= -k
        Expression expr2 = ctx.addExpression("dist2LE_neg_" + ctr.num);
        expr2.set(ctx.getLpVar(x), 1);
        expr2.set(ctx.getLpVar(y), -1);
        expr2.lower(-k);

        return true;
    }

    /**
     * |x - y| >= k
     * This is disjunctive: (x - y >= k) OR (y - x >= k)
     * Uses big-M relaxation with auxiliary binary.
     */
    private boolean addDist2GE(Primitive2 ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        int k = getK(ctr);

        // Compute big-M values
        double Mpos = k - (x.dom.firstValue() - y.dom.lastValue()); // for x - y >= k
        double Mneg = k - (y.dom.firstValue() - x.dom.lastValue()); // for y - x >= k

        if (Mpos <= 0 || Mneg <= 0) {
            // One branch is always satisfied
            return true;
        }

        // Create auxiliary binary b: b=1 means "x - y >= k" is the active branch
        org.ojalgo.optimisation.Variable b = org.ojalgo.optimisation.Variable
            .make("dist2GE_" + ctr.num + "_b").lower(0).upper(1);
        ctx.addVariable(b);

        // x - y >= k - M*(1-b)  =>  x - y + M*b >= k - M + M = k
        // Actually: x - y >= k when b=1, relaxed when b=0
        // x - y - M*(1-b) >= k - M  =>  x - y + M*b >= k
        Expression expr1 = ctx.addExpression("dist2GE_pos_" + ctr.num);
        expr1.set(ctx.getLpVar(x), 1);
        expr1.set(ctx.getLpVar(y), -1);
        expr1.set(b, Mpos);
        expr1.lower(k);

        // y - x >= k when b=0, i.e., y - x + M*b >= k
        // Actually we need: y - x >= k - M*b
        // y - x + M*b >= k
        Expression expr2 = ctx.addExpression("dist2GE_neg_" + ctr.num);
        expr2.set(ctx.getLpVar(y), 1);
        expr2.set(ctx.getLpVar(x), -1);
        expr2.set(b, -Mneg);
        expr2.lower(k - Mneg);

        return true;
    }

    /**
     * |x - y| = k  =>  (x - y = k) OR (x - y = -k)
     * LP relaxation: -k <= x - y <= k (valid but weak)
     */
    private boolean addDist2EQ(Primitive2 ctr, LinearizationContext ctx) {
        // Use the LE relaxation as a valid approximation
        return addDist2LE(ctr, ctx);
    }

    /**
     * x = |y - k|: means x >= 0 and (x = y - k OR x = k - y)
     * LP relaxation: x >= y - k AND x >= k - y (equivalent to x >= |y - k|)
     */
    private boolean addDist2bEQ(Primitive2 ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];
        int k = getK(ctr);

        // x >= y - k  =>  x - y >= -k
        Expression expr1 = ctx.addExpression("dist2bEQ_pos_" + ctr.num);
        expr1.set(ctx.getLpVar(x), 1);
        expr1.set(ctx.getLpVar(y), -1);
        expr1.lower(-k);

        // x >= k - y  =>  x + y >= k
        Expression expr2 = ctx.addExpression("dist2bEQ_neg_" + ctr.num);
        expr2.set(ctx.getLpVar(x), 1);
        expr2.set(ctx.getLpVar(y), 1);
        expr2.lower(k);

        return true;
    }

    /**
     * Disjunctive constraint: (x + wx <= y) OR (y + wy <= x)
     * Uses big-M formulation.
     */
    private boolean addDisjonctive(Disjonctive ctr, LinearizationContext ctx) {
        Variable x = ctr.scp[0];
        Variable y = ctr.scp[1];

        // Get wx, wy via reflection
        int wx, wy;
        try {
            java.lang.reflect.Field wxField = Disjonctive.class.getDeclaredField("wx");
            java.lang.reflect.Field wyField = Disjonctive.class.getDeclaredField("wy");
            wxField.setAccessible(true);
            wyField.setAccessible(true);
            wx = (int) wxField.get(ctr);
            wy = (int) wyField.get(ctr);
        } catch (Exception e) {
            return false;
        }

        // Big-M values
        double M1 = x.dom.lastValue() + wx - y.dom.firstValue();
        double M2 = y.dom.lastValue() + wy - x.dom.firstValue();

        // Create auxiliary binary b: b=1 means x + wx <= y
        org.ojalgo.optimisation.Variable b = org.ojalgo.optimisation.Variable
            .make("disj_" + ctr.num + "_b").lower(0).upper(1);
        ctx.addVariable(b);

        // x + wx <= y + M*(1-b)  =>  x - y <= -wx + M - M*b  =>  x - y + M*b <= M - wx
        Expression expr1 = ctx.addExpression("disj_xy_" + ctr.num);
        expr1.set(ctx.getLpVar(x), 1);
        expr1.set(ctx.getLpVar(y), -1);
        expr1.set(b, M1);
        expr1.upper(M1 - wx);

        // y + wy <= x + M*b  =>  y - x <= -wy + M*b  =>  y - x - M*b <= -wy
        Expression expr2 = ctx.addExpression("disj_yx_" + ctr.num);
        expr2.set(ctx.getLpVar(y), 1);
        expr2.set(ctx.getLpVar(x), -1);
        expr2.set(b, -M2);
        expr2.upper(-wy);

        registerDisjunctiveNoOverlapCut(x, wx, y, wy, b, ctx);

        return true;
    }

    private void registerDisjunctiveNoOverlapCut(Variable x, int wx, Variable y, int wy, org.ojalgo.optimisation.Variable selector,
            LinearizationContext ctx) {
        DisjunctiveRegistry registry = ctx.getOrCreateMetadata(DISJUNCTIVE_REGISTRY_KEY, () -> {
            DisjunctiveRegistry created = new DisjunctiveRegistry();
            ctx.registerCutGenerator(new NoOverlapTriangleCutGenerator(created));
            return created;
        });
        registry.add(new TaskKey(x.num, wx), x, new TaskKey(y.num, wy), y, selector);
    }
}
