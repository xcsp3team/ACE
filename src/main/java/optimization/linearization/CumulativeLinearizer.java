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

import java.util.HashSet;
import java.util.Set;

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
 * This mirrors the "base relaxation" part of CP-SAT more closely than the
 * previous ad hoc linearization:
 * - a horizon energy inequality over the current bounding box;
 * - pairwise capacity constraints only for mandatory overlaps;
 * - pairwise disjunctions only when the minimum combined demand exceeds the
 *   current capacity upper bound.
 */
public class CumulativeLinearizer implements ConstraintLinearizer {

    private static final double CUT_VIOLATION_EPS = 1e-6;
    private static final int MAX_TIMETABLE_CUTS_PER_ROUND = 5;

    private static final class CumulativeData {
        Variable[] starts;
        int[] widths;
        int[] heights;
        int limit;
        int nTasks;
        boolean movableWidths;
        boolean movableHeights;
        Variable[] widthVars;
        Variable[] heightVars;
        Variable limitVar;

        int minWidth(int i) {
            return widthVars == null ? widths[i] : widthVars[i].dom.firstValue();
        }

        int maxWidth(int i) {
            return widthVars == null ? widths[i] : widthVars[i].dom.lastValue();
        }

        int minHeight(int i) {
            return heightVars == null ? heights[i] : heightVars[i].dom.firstValue();
        }

        int maxCapacity() {
            return limitVar == null ? limit : limitVar.dom.lastValue();
        }

        int initialStartMin(int i) {
            return starts[i].dom.smallestInitialValue();
        }

        int initialStartMax(int i) {
            return starts[i].dom.greatestInitialValue();
        }

        int initialMinWidth(int i) {
            return widthVars == null ? widths[i] : widthVars[i].dom.smallestInitialValue();
        }
    }

    private static final class CumulativeTimeTableCutGenerator implements LpCutGenerator {
        private final int constraintNum;
        private final CumulativeData data;
        private final Set<String> emittedCuts = new HashSet<>();

        CumulativeTimeTableCutGenerator(Cumulative ctr, CumulativeData data) {
            this.constraintNum = ctr.num;
            this.data = data;
        }

        @Override
        public String name() {
            return "CumulativeTimeTable";
        }

        @Override
        public int generateCuts(CutGenerationContext ctx) {
            int cuts = 0;
            for (int i = 0; i < data.nTasks && cuts < MAX_TIMETABLE_CUTS_PER_ROUND; i++) {
                int timePoint = data.initialStartMax(i);
                if (mandatoryEnd(i) <= timePoint)
                    continue;

                double demandLp = 0d;
                long constantDemand = 0L;
                StringBuilder signature = new StringBuilder();
                for (int j = 0; j < data.nTasks; j++) {
                    if (!isMandatoryAt(j, timePoint))
                        continue;
                    signature.append(j).append(',');
                    if (data.heightVars == null) {
                        int height = data.minHeight(j);
                        constantDemand += height;
                        demandLp += height;
                    } else {
                        demandLp += ctx.getLpValue(data.heightVars[j]);
                    }
                }
                if (signature.length() == 0)
                    continue;

                double capacityLp = data.limitVar == null ? data.limit : ctx.getLpValue(data.limitVar);
                if (demandLp <= capacityLp + CUT_VIOLATION_EPS)
                    continue;

                String key = signature.toString();
                if (!emittedCuts.add(key))
                    continue;

                Expression cut = ctx.addExpression("cumul_tt_" + constraintNum + "_" + ctx.nextGeneratedCutId());
                if (data.heightVars == null) {
                    if (data.limitVar == null) {
                        cut.upper(data.limit - constantDemand);
                    } else {
                        cut.set(ctx.getLpVar(data.limitVar), -1);
                        cut.upper(-constantDemand);
                    }
                } else {
                    for (int j = 0; j < data.nTasks; j++) {
                        if (isMandatoryAt(j, timePoint))
                            cut.set(ctx.getLpVar(data.heightVars[j]), 1);
                    }
                    if (data.limitVar == null) {
                        cut.upper(data.limit);
                    } else {
                        cut.set(ctx.getLpVar(data.limitVar), -1);
                        cut.upper(0);
                    }
                }
                cuts++;
            }
            return cuts;
        }

        private int mandatoryEnd(int i) {
            return data.initialStartMin(i) + data.initialMinWidth(i);
        }

        private boolean isMandatoryAt(int i, int timePoint) {
            int startMax = data.initialStartMax(i);
            int endMin = mandatoryEnd(i);
            return startMax <= timePoint && timePoint < endMin;
        }
    }

    @Override
    public boolean canLinearize(Constraint c) {
        return c instanceof Cumulative;
    }

    @Override
    public boolean linearize(Constraint c, LinearizationContext ctx) {
        Cumulative ctr = (Cumulative) c;
        CumulativeData data = extract(ctr);
        if (data == null)
            return false;

        int minStart = Integer.MAX_VALUE;
        int maxEnd = Integer.MIN_VALUE;
        for (int i = 0; i < data.nTasks; i++) {
            minStart = Math.min(minStart, data.starts[i].dom.firstValue());
            maxEnd = Math.max(maxEnd, data.starts[i].dom.lastValue() + data.maxWidth(i));
        }
        int horizon = maxEnd - minStart;
        if (horizon <= 0)
            horizon = 1;

        addEndBounds(ctr, data, maxEnd, ctx);
        addEnergyRelaxation(ctr, data, horizon, ctx);
        addMandatoryOverlapCapacityConstraints(ctr, data, ctx);
        addMandatoryDisjunctions(ctr, data, ctx);
        ctx.registerCutGenerator(new CumulativeTimeTableCutGenerator(ctr, data));
        return true;
    }

    private CumulativeData extract(Cumulative ctr) {
        CumulativeData data = new CumulativeData();
        try {
            java.lang.reflect.Field startsField = Cumulative.class.getDeclaredField("starts");
            java.lang.reflect.Field widthsField = Cumulative.class.getDeclaredField("wwidths");
            java.lang.reflect.Field heightsField = Cumulative.class.getDeclaredField("wheights");
            java.lang.reflect.Field limitField = Cumulative.class.getDeclaredField("limit");
            java.lang.reflect.Field nTasksField = Cumulative.class.getDeclaredField("nTasks");
            java.lang.reflect.Field movableWidthsField = Cumulative.class.getDeclaredField("movableWidths");
            java.lang.reflect.Field movableHeightsField = Cumulative.class.getDeclaredField("movableHeights");

            startsField.setAccessible(true);
            widthsField.setAccessible(true);
            heightsField.setAccessible(true);
            limitField.setAccessible(true);
            nTasksField.setAccessible(true);
            movableWidthsField.setAccessible(true);
            movableHeightsField.setAccessible(true);

            data.starts = (Variable[]) startsField.get(ctr);
            data.widths = (int[]) widthsField.get(ctr);
            data.heights = (int[]) heightsField.get(ctr);
            data.limit = (int) limitField.get(ctr);
            data.nTasks = (int) nTasksField.get(ctr);
            data.movableWidths = (boolean) movableWidthsField.get(ctr);
            data.movableHeights = (boolean) movableHeightsField.get(ctr);
        } catch (Exception e) {
            return null;
        }

        int offset = data.nTasks;
        if (data.movableWidths) {
            data.widthVars = new Variable[data.nTasks];
            System.arraycopy(ctr.scp, offset, data.widthVars, 0, data.nTasks);
            offset += data.nTasks;
        }
        if (data.movableHeights) {
            data.heightVars = new Variable[data.nTasks];
            System.arraycopy(ctr.scp, offset, data.heightVars, 0, data.nTasks);
            offset += data.nTasks;
        }
        if (ctr instanceof Cumulative.CumulativeVarC
                || ctr instanceof Cumulative.CumulativeVarWC
                || ctr instanceof Cumulative.CumulativeVarHC
                || ctr instanceof Cumulative.CumulativeVarWHC) {
            data.limitVar = ctr.scp[ctr.scp.length - 1];
        }
        return data;
    }

    private void addEndBounds(Cumulative ctr, CumulativeData data, int maxEnd, LinearizationContext ctx) {
        for (int i = 0; i < data.nTasks; i++) {
            Expression endExpr = ctx.addExpression("cumul_end_" + ctr.num + "_" + i);
            endExpr.set(ctx.getLpVar(data.starts[i]), 1);
            if (data.widthVars == null) {
                endExpr.upper(maxEnd - data.widths[i]);
            } else {
                endExpr.set(ctx.getLpVar(data.widthVars[i]), 1);
                endExpr.upper(maxEnd);
            }
        }
    }

    private void addEnergyRelaxation(Cumulative ctr, CumulativeData data, int horizon, LinearizationContext ctx) {
        if (data.nTasks == 0)
            return;

        if (data.widthVars == null && data.heightVars == null && data.limitVar == null)
            return;

        if (data.widthVars != null && data.heightVars != null) {
            addLowerBoundEnergyFromWidths(ctr, data, horizon, ctx);
            addLowerBoundEnergyFromHeights(ctr, data, horizon, ctx);
            return;
        }
        if (data.widthVars != null) {
            addLowerBoundEnergyFromWidths(ctr, data, horizon, ctx);
            return;
        }
        if (data.heightVars != null) {
            addLowerBoundEnergyFromHeights(ctr, data, horizon, ctx);
            return;
        }

        long totalEnergy = 0;
        for (int i = 0; i < data.nTasks; i++)
            totalEnergy += (long) data.widths[i] * data.heights[i];

        Expression expr = ctx.addExpression("cumul_energy_" + ctr.num);
        expr.set(ctx.getLpVar(data.limitVar), -horizon);
        expr.upper(-totalEnergy);
    }

    private void addLowerBoundEnergyFromWidths(Cumulative ctr, CumulativeData data, int horizon, LinearizationContext ctx) {
        Expression expr = ctx.addExpression("cumul_energy_w_" + ctr.num);
        for (int i = 0; i < data.nTasks; i++) {
            int demandLb = data.minHeight(i);
            if (demandLb == 0)
                continue;
            expr.set(ctx.getLpVar(data.widthVars[i]), demandLb);
        }
        if (data.limitVar == null) {
            expr.upper((long) data.limit * horizon);
        } else {
            expr.set(ctx.getLpVar(data.limitVar), -horizon);
            expr.upper(0);
        }
    }

    private void addLowerBoundEnergyFromHeights(Cumulative ctr, CumulativeData data, int horizon, LinearizationContext ctx) {
        Expression expr = ctx.addExpression("cumul_energy_h_" + ctr.num);
        for (int i = 0; i < data.nTasks; i++) {
            int widthLb = data.minWidth(i);
            if (widthLb == 0)
                continue;
            expr.set(ctx.getLpVar(data.heightVars[i]), widthLb);
        }
        if (data.limitVar == null) {
            expr.upper((long) data.limit * horizon);
        } else {
            expr.set(ctx.getLpVar(data.limitVar), -horizon);
            expr.upper(0);
        }
    }

    private void addMandatoryOverlapCapacityConstraints(Cumulative ctr, CumulativeData data, LinearizationContext ctx) {
        int maxPairs = Math.min(100, data.nTasks * (data.nTasks - 1) / 2);
        int added = 0;
        for (int i = 0; i < data.nTasks && added < maxPairs; i++) {
            for (int j = i + 1; j < data.nTasks && added < maxPairs; j++) {
                if (!mustOverlap(data, i, j))
                    continue;

                if (data.heightVars == null) {
                    long pairDemand = (long) data.heights[i] + data.heights[j];
                    if (data.limitVar == null) {
                        if (pairDemand > data.limit) {
                            Expression expr = ctx.addExpression("cumul_overlap_" + ctr.num + "_" + i + "_" + j);
                            expr.lower(1);
                            added++;
                        }
                    } else {
                        Expression expr = ctx.addExpression("cumul_overlap_" + ctr.num + "_" + i + "_" + j);
                        expr.set(ctx.getLpVar(data.limitVar), -1);
                        expr.upper(-pairDemand);
                        added++;
                    }
                } else {
                    Expression expr = ctx.addExpression("cumul_overlap_" + ctr.num + "_" + i + "_" + j);
                    expr.set(ctx.getLpVar(data.heightVars[i]), 1);
                    expr.set(ctx.getLpVar(data.heightVars[j]), 1);
                    if (data.limitVar == null)
                        expr.upper(data.limit);
                    else {
                        expr.set(ctx.getLpVar(data.limitVar), -1);
                        expr.upper(0);
                    }
                    added++;
                }
            }
        }
    }

    private void addMandatoryDisjunctions(Cumulative ctr, CumulativeData data, LinearizationContext ctx) {
        int maxPairs = Math.min(100, data.nTasks * (data.nTasks - 1) / 2);
        int added = 0;
        int capacityUpper = data.maxCapacity();
        for (int i = 0; i < data.nTasks && added < maxPairs; i++) {
            for (int j = i + 1; j < data.nTasks && added < maxPairs; j++) {
                if (!canPossiblyOverlap(data, i, j))
                    continue;
                if ((long) data.minHeight(i) + data.minHeight(j) <= capacityUpper)
                    continue;
                addDisjunctiveConstraint(ctr, data, i, j, ctx);
                added++;
            }
        }
    }

    private boolean canPossiblyOverlap(CumulativeData data, int i, int j) {
        int startMinI = data.starts[i].dom.firstValue();
        int startMaxI = data.starts[i].dom.lastValue();
        int startMinJ = data.starts[j].dom.firstValue();
        int startMaxJ = data.starts[j].dom.lastValue();
        return !(startMaxI + data.maxWidth(i) <= startMinJ || startMaxJ + data.maxWidth(j) <= startMinI);
    }

    private boolean mustOverlap(CumulativeData data, int i, int j) {
        int startMinI = data.starts[i].dom.firstValue();
        int startMaxI = data.starts[i].dom.lastValue();
        int startMinJ = data.starts[j].dom.firstValue();
        int startMaxJ = data.starts[j].dom.lastValue();
        return startMinI + data.minWidth(i) > startMaxJ && startMinJ + data.minWidth(j) > startMaxI;
    }

    /**
     * Add disjunctive constraint: task i finishes before j starts, OR j finishes before i starts.
     */
    private void addDisjunctiveConstraint(Cumulative ctr, CumulativeData data, int i, int j, LinearizationContext ctx) {
        Variable si = data.starts[i];
        Variable sj = data.starts[j];

        double M1 = si.dom.lastValue() + data.maxWidth(i) - sj.dom.firstValue();
        double M2 = sj.dom.lastValue() + data.maxWidth(j) - si.dom.firstValue();
        if (M1 <= 0 || M2 <= 0)
            return;

        org.ojalgo.optimisation.Variable b = org.ojalgo.optimisation.Variable
            .make("cumul_disj_" + ctr.num + "_" + i + "_" + j).lower(0).upper(1);
        ctx.addVariable(b);

        Expression expr1 = ctx.addExpression("cumul_disj_ij_" + ctr.num + "_" + i + "_" + j);
        expr1.set(ctx.getLpVar(si), 1);
        expr1.set(ctx.getLpVar(sj), -1);
        if (data.widthVars == null)
            expr1.upper(M1 - data.widths[i]);
        else {
            expr1.set(ctx.getLpVar(data.widthVars[i]), 1);
            expr1.upper(M1);
        }
        expr1.set(b, M1);

        Expression expr2 = ctx.addExpression("cumul_disj_ji_" + ctr.num + "_" + i + "_" + j);
        expr2.set(ctx.getLpVar(sj), 1);
        expr2.set(ctx.getLpVar(si), -1);
        if (data.widthVars == null)
            expr2.upper(-data.widths[j]);
        else {
            expr2.set(ctx.getLpVar(data.widthVars[j]), 1);
            expr2.upper(0);
        }
        expr2.set(b, -M2);
    }
}
