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

import org.ojalgo.optimisation.ExpressionsBasedModel;
import org.ojalgo.optimisation.Optimisation;
import org.ojalgo.optimisation.solver.cplex.SolverCPLEX;

import ilog.concert.IloException;
import ilog.cplex.IloCplex;

/**
 * Minimal wrapper around ojAlgo's SolverCPLEX that exposes CPLEX best bound
 * separately from Result.getValue() (which remains primal objective).
 */
public final class BoundAwareSolverCPLEX implements Optimisation.Solver {

    private static final double CPLEX_HUGE = 1.0E70;

    private static final ThreadLocal<Double> LAST_BEST_BOUND = ThreadLocal.withInitial(() -> Double.NaN);

    private static final Field SOLVER_FIELD = BoundAwareSolverCPLEX.initSolverField();

    static final class Integration extends ExpressionsBasedModel.Integration<BoundAwareSolverCPLEX> {

        private static final ExpressionsBasedModel.Integration<SolverCPLEX> DELEGATE_INTEGRATION = SolverCPLEX.INTEGRATION;

        @Override
        public BoundAwareSolverCPLEX build(final ExpressionsBasedModel model) {
            SolverCPLEX delegate = DELEGATE_INTEGRATION.build(model);
            return new BoundAwareSolverCPLEX(delegate, BoundAwareSolverCPLEX.extractCplex(delegate));
        }

        @Override
        public boolean isCapable(final ExpressionsBasedModel model) {
            return DELEGATE_INTEGRATION.isCapable(model);
        }

        @Override
        protected boolean isSolutionMapped() {
            return true;
        }
    }

    public static final ExpressionsBasedModel.Integration<BoundAwareSolverCPLEX> INTEGRATION = new Integration();

    public static double getLastBestBound() {
        return LAST_BEST_BOUND.get();
    }

    private static IloCplex extractCplex(final SolverCPLEX delegate) {

        if (SOLVER_FIELD == null) {
            return null;
        }

        try {
            return (IloCplex) SOLVER_FIELD.get(delegate);
        } catch (IllegalAccessException e) {
            return null;
        }
    }

    private static Field initSolverField() {

        for (String fieldName : new String[] { "myDelegateSolver", "mySolver" }) {
            try {
                Field field = SolverCPLEX.class.getDeclaredField(fieldName);
                field.setAccessible(true);
                return field;
            } catch (ReflectiveOperationException | RuntimeException ignored) {
            }
        }
        return null;
    }

    private final IloCplex cplex;
    private final SolverCPLEX delegate;

    private BoundAwareSolverCPLEX(final SolverCPLEX delegate, final IloCplex cplex) {
        this.delegate = delegate;
        this.cplex = cplex;
    }

    @Override
    public void dispose() {
        delegate.dispose();
    }

    @Override
    public Optimisation.Result solve(final Optimisation.Result kickStarter) {

        LAST_BEST_BOUND.set(Double.NaN);

        Optimisation.Result result = delegate.solve(kickStarter);

        if (cplex != null) {
            try {
                if (cplex.isMIP()) {
                    double bestBound = cplex.getBestObjValue();
                    if (Double.isFinite(bestBound) && Math.abs(bestBound) < CPLEX_HUGE) {
                        LAST_BEST_BOUND.set(bestBound);
                    }
                }
            } catch (IloException ignored) {
                // No best bound available for this status/problem type.
            }
        }

        return result;
    }
}
