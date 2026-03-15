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
import java.util.HashSet;
import java.util.List;
import java.util.NavigableSet;
import java.util.Set;
import java.util.TreeSet;

import org.ojalgo.optimisation.Expression;

import constraints.Constraint;
import constraints.global.AllDifferent;
import variables.Domain;
import variables.Variable;

/**
 * Linearizer for AllDifferent constraints.
 *
 * Following CP-SAT:
 * - permutation-like cases get a static linear relaxation: sum(x_i) = sum(V)
 * - the general case is strengthened by a cut generator on LP-sorted subsets
 */
public final class AllDifferentLinearizer implements ConstraintLinearizer {

    private static final double CUT_VIOLATION_EPS = 1e-6;
    private static final int MAX_CUT_SIZE = 16;
    private static final int MAX_CUTS_PER_ROUND = 5;

    private static final class AllDifferentCutGenerator implements LpCutGenerator {
        private final int constraintNum;
        private final Variable[] variables;
        private final Set<String> emittedCuts = new HashSet<>();

        AllDifferentCutGenerator(AllDifferent ctr) {
            this.constraintNum = ctr.num;
            this.variables = ctr.scp;
        }

        @Override
        public String name() {
            return "AllDifferent";
        }

        @Override
        public int generateCuts(CutGenerationContext ctx) {
            List<Variable> active = new ArrayList<>();
            for (Variable x : variables) {
                if (x.dom.size() > 1)
                    active.add(x);
            }
            if (active.size() <= 2 || active.size() > MAX_CUT_SIZE)
                return 0;

            int cuts = generateDirectionalCuts(ctx, active, true);
            if (cuts >= MAX_CUTS_PER_ROUND)
                return cuts;
            return cuts + generateDirectionalCuts(ctx, active, false);
        }

        private int generateDirectionalCuts(CutGenerationContext ctx, List<Variable> active, boolean ascending) {
            active.sort((x, y) -> {
                int byValue = Double.compare(ctx.getLpValue(x), ctx.getLpValue(y));
                if (!ascending)
                    byValue = -byValue;
                if (byValue != 0)
                    return byValue;
                return Integer.compare(x.num, y.num);
            });

            int cuts = 0;
            double lpSum = 0d;
            List<Variable> prefix = new ArrayList<>();
            NavigableSet<Integer> unionValues = new TreeSet<>();

            for (Variable x : active) {
                prefix.add(x);
                lpSum += ctx.getLpValue(x);
                addDomainValues(unionValues, x.dom);
                int prefixSize = prefix.size();
                if (unionValues.size() < prefixSize)
                    continue;

                long required = ascending ? sumSmallest(unionValues, prefixSize) : sumLargest(unionValues, prefixSize);
                boolean violated = ascending ? lpSum < required - CUT_VIOLATION_EPS : lpSum > required + CUT_VIOLATION_EPS;
                if (!violated)
                    continue;

                String signature = signature(prefix, ascending);
                if (!emittedCuts.add(signature))
                    continue;

                Expression cut = ctx.addExpression("alldiff_" + constraintNum + "_" + ctx.nextGeneratedCutId());
                for (Variable var : prefix)
                    cut.set(ctx.getLpVar(var), 1);
                if (ascending)
                    cut.lower(required);
                else
                    cut.upper(required);
                cuts++;
                if (cuts >= MAX_CUTS_PER_ROUND)
                    break;

                // As in CP-SAT, restart from a fresh subset after a violated prefix.
                lpSum = 0d;
                prefix.clear();
                unionValues.clear();
            }
            return cuts;
        }

        private static void addDomainValues(NavigableSet<Integer> values, Domain dom) {
            for (int a = dom.first(); a != -1; a = dom.next(a))
                values.add(dom.toVal(a));
        }

        private static long sumSmallest(NavigableSet<Integer> values, int count) {
            long sum = 0;
            int seen = 0;
            for (int value : values) {
                sum += value;
                if (++seen >= count)
                    break;
            }
            return sum;
        }

        private static long sumLargest(NavigableSet<Integer> values, int count) {
            long sum = 0;
            int seen = 0;
            for (int value : values.descendingSet()) {
                sum += value;
                if (++seen >= count)
                    break;
            }
            return sum;
        }

        private static String signature(List<Variable> prefix, boolean ascending) {
            StringBuilder sb = new StringBuilder(ascending ? "lb:" : "ub:");
            for (Variable x : prefix)
                sb.append(x.num).append(',');
            return sb.toString();
        }
    }

    @Override
    public boolean canLinearize(Constraint c) {
        return c instanceof AllDifferent.AllDifferentComplete
            || c instanceof AllDifferent.AllDifferentPermutation
            || c instanceof AllDifferent.AllDifferentWeak
            || c instanceof AllDifferent.AllDifferentCounting;
    }

    @Override
    public boolean linearize(Constraint c, LinearizationContext ctx) {
        AllDifferent ctr = (AllDifferent) c;
        Variable[] list = ctr.scp;

        if (isPermutationLike(list)) {
            addPermutationRelaxation(ctr, list, ctx);
        } else if (list.length <= MAX_CUT_SIZE) {
            ctx.registerCutGenerator(new AllDifferentCutGenerator(ctr));
        } else {
            return false;
        }
        return true;
    }

    private boolean isPermutationLike(Variable[] list) {
        NavigableSet<Integer> unionValues = new TreeSet<>();
        for (Variable x : list)
            addCurrentDomainValues(unionValues, x.dom);
        return unionValues.size() == list.length;
    }

    private void addPermutationRelaxation(AllDifferent ctr, Variable[] list, LinearizationContext ctx) {
        NavigableSet<Integer> unionValues = new TreeSet<>();
        for (Variable x : list)
            addCurrentDomainValues(unionValues, x.dom);

        long sum = 0;
        for (int value : unionValues)
            sum += value;

        Expression expr = ctx.addExpression("alldiff_perm_" + ctr.num);
        for (Variable x : list)
            expr.set(ctx.getLpVar(x), 1);
        expr.level(sum);
    }

    private static void addCurrentDomainValues(NavigableSet<Integer> values, Domain dom) {
        for (int a = dom.first(); a != -1; a = dom.next(a))
            values.add(dom.toVal(a));
    }
}
