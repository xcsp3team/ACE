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
import java.math.BigDecimal;
import java.util.List;

import org.ojalgo.netio.BasicLogger;
import org.ojalgo.optimisation.Expression;
import org.ojalgo.optimisation.ExpressionsBasedModel;
import org.ojalgo.optimisation.Optimisation;
import org.ojalgo.optimisation.Variable;
import org.ojalgo.structure.Structure1D.IntIndex;
import org.ojalgo.structure.Structure2D.IntRowColumn;

import ilog.concert.IloException;
import ilog.concert.IloLQNumExpr;
import ilog.concert.IloLinearNumExpr;
import ilog.concert.IloNumExpr;
import ilog.concert.IloNumVar;
import ilog.concert.IloNumVarType;
import ilog.concert.IloQuadNumExpr;
import ilog.cplex.IloCplex;
import ilog.cplex.IloCplex.IntParam;
import ilog.cplex.IloCplex.Status;

/**
 * Local CPLEX integration that preserves a useful bound in Result.value when the solve
 * stops before optimality (time/iteration/user limits).
 */
public final class BoundAwareSolverCPLEX implements Optimisation.Solver {

    private static final ThreadLocal<Double> LAST_BEST_BOUND = ThreadLocal.withInitial(() -> Double.NaN);

    public static class Configurator {

        protected IloCplex newIloCplex(final Optimisation.Options options) throws IloException {

            IloCplex retVal = new IloCplex();

            if (options.logger_appender != null) {

                retVal.setParam(IntParam.MIPDisplay, 5);
                retVal.setParam(IntParam.MIPInterval, 5);

                retVal.setOut(new OutputStream() {

                    @Override
                    public void write(final int b) throws IOException {
                        options.logger_appender.print((char) b);
                    }
                });

            } else {

                retVal.setOut(OutputStream.nullOutputStream());
            }

            return retVal;
        }
    }

    static final class Integration extends ExpressionsBasedModel.Integration<BoundAwareSolverCPLEX> {

        @Override
        public BoundAwareSolverCPLEX build(final ExpressionsBasedModel model) {

            try {

                Configurator configurator = model.options.getConfigurator(Configurator.class).orElse(DEFAULT);
                IloCplex solver = configurator.newIloCplex(model.options);

                boolean mip = model.isAnyVariableInteger();

                List<Variable> mVars = model.getVariables();
                int nbVars = mVars.size();

                IloNumVar[] sVars = new IloNumVar[nbVars];

                for (int i = 0; i < nbVars; i++) {

                    Variable mVar = mVars.get(i);

                    IloNumVarType type = IloNumVarType.Float;
                    if (mip) {
                        if (mVar.isBinary()) {
                            type = IloNumVarType.Bool;
                        } else if (mVar.isInteger()) {
                            type = IloNumVarType.Int;
                        }
                    }
                    double lb = BoundAwareSolverCPLEX.asDouble(mVar.getLowerLimit(), Double.NEGATIVE_INFINITY);
                    double ub = BoundAwareSolverCPLEX.asDouble(mVar.getUpperLimit(), Double.POSITIVE_INFINITY);
                    String name = mVar.getName();

                    solver.add(sVars[i] = solver.numVar(lb, ub, type, name));
                }

                model.constraints().forEach(mConstr -> {

                    try {

                        IloNumExpr sConstr = this.buildExpression(mConstr, solver, sVars);

                        if (mConstr.isEqualityConstraint()) {
                            solver.addEq(BoundAwareSolverCPLEX.asDouble(mConstr.getLowerLimit(), 0.0), sConstr);
                        } else {
                            if (mConstr.isLowerConstraint()) {
                                solver.addLe(BoundAwareSolverCPLEX.asDouble(mConstr.getLowerLimit(), Double.NEGATIVE_INFINITY), sConstr);
                            }
                            if (mConstr.isUpperConstraint()) {
                                solver.addGe(BoundAwareSolverCPLEX.asDouble(mConstr.getUpperLimit(), Double.POSITIVE_INFINITY), sConstr);
                            }
                        }

                    } catch (IloException cause) {
                        throw new RuntimeException(cause);
                    }
                });

                Expression mObj = model.objective();
                IloNumExpr sObj = this.buildExpression(mObj, solver, sVars);

                if (model.isMaximisation()) {
                    solver.addMaximize(sObj);
                } else {
                    solver.addMinimize(sObj);
                }

                return new BoundAwareSolverCPLEX(solver, sVars);

            } catch (IloException cause) {
                throw new RuntimeException(cause);
            }
        }

        @Override
        public boolean isCapable(final ExpressionsBasedModel model) {
            return true;
        }

        @Override
        protected boolean isSolutionMapped() {
            return false;
        }

        private void copyLinear(final Expression source, final IloNumVar[] variables, final IloLinearNumExpr destination) throws IloException {
            for (IntIndex key : source.getLinearKeySet()) {
                destination.addTerm(source.getAdjustedLinearFactor(key), variables[key.index]);
            }
        }

        private void copyQuadratic(final Expression source, final IloNumVar[] variables, final IloQuadNumExpr destination) throws IloException {
            for (IntRowColumn key : source.getQuadraticKeySet()) {
                destination.addTerm(source.getAdjustedQuadraticFactor(key), variables[key.row], variables[key.column]);
            }
        }

        IloNumExpr buildExpression(final Expression expression, final IloCplex cplex, final IloNumVar[] variables) throws IloException {

            if (expression.isFunctionQuadratic()) {

                IloLQNumExpr tmpIloLQNumExpr = cplex.lqNumExpr();

                this.copyQuadratic(expression, variables, tmpIloLQNumExpr);
                this.copyLinear(expression, variables, tmpIloLQNumExpr);

                return tmpIloLQNumExpr;

            } else if (expression.isFunctionPureQuadratic()) {

                IloQuadNumExpr tmpIloQuadNumExpr = cplex.quadNumExpr();

                this.copyQuadratic(expression, variables, tmpIloQuadNumExpr);

                return tmpIloQuadNumExpr;

            } else if (expression.isFunctionLinear()) {

                IloLinearNumExpr tmpIloLinearNumExpr = cplex.linearNumExpr();

                this.copyLinear(expression, variables, tmpIloLinearNumExpr);

                return tmpIloLinearNumExpr;

            } else {

                return cplex.linearNumExpr();
            }
        }
    }

    public static final ExpressionsBasedModel.Integration<BoundAwareSolverCPLEX> INTEGRATION = new Integration();

    static final Configurator DEFAULT = new Configurator();

    private static double asDouble(final BigDecimal value, final double defaultValue) {
        return value != null ? value.doubleValue() : defaultValue;
    }

    public static double getLastBestBound() {
        return LAST_BEST_BOUND.get();
    }

    static Optimisation.State translate(final IloCplex.Status status) {
        if (status.equals(Status.Bounded)) {
            return Optimisation.State.VALID;
        } else if (status.equals(Status.Error)) {
            return Optimisation.State.FAILED;
        } else if (status.equals(Status.Feasible)) {
            return Optimisation.State.FEASIBLE;
        } else if (status.equals(Status.Infeasible)) {
            return Optimisation.State.INFEASIBLE;
        } else if (status.equals(Status.InfeasibleOrUnbounded)) {
            return Optimisation.State.INVALID;
        } else if (status.equals(Status.Optimal)) {
            return Optimisation.State.OPTIMAL;
        } else if (status.equals(Status.Unbounded)) {
            return Optimisation.State.UNBOUNDED;
        } else if (status.equals(Status.Unknown)) {
            return Optimisation.State.UNEXPLORED;
        } else {
            return Optimisation.State.FAILED;
        }
    }

    private final IloCplex mySolver;
    private final IloNumVar[] myVariables;

    BoundAwareSolverCPLEX(final IloCplex solver, final IloNumVar[] variables) {
        super();
        mySolver = solver;
        myVariables = variables;
    }

    @Override
    public void dispose() {

        Solver.super.dispose();

        if (mySolver != null) {
            mySolver.end();
        }
    }

    @Override
    public Optimisation.Result solve(final Optimisation.Result kickStarter) {

        double retValue = Double.NaN;
        Optimisation.State retState = Optimisation.State.UNEXPLORED;
        double[] retSolution = new double[myVariables.length];
        LAST_BEST_BOUND.set(Double.NaN);

        try {

            boolean solved = mySolver.solve();
            boolean primalFeasible = mySolver.isPrimalFeasible();

            if (solved || primalFeasible) {
                for (int i = 0; i < myVariables.length; i++) {
                    retSolution[i] = mySolver.getValue(myVariables[i]);
                }
            }

            if (solved || primalFeasible) {
                retValue = mySolver.getObjValue();
            }

            try {
                double bestBound = this.readBestBound();
                if (Double.isFinite(bestBound)) {
                    LAST_BEST_BOUND.set(bestBound);
                }
            } catch (IloException ignored) {
                // No dual/best bound available from CPLEX for this solve status/type.
            }

            retState = BoundAwareSolverCPLEX.translate(mySolver.getStatus());

            if (retState == Optimisation.State.FAILED || retState == Optimisation.State.UNEXPLORED) {
                // CPLEX "abort" statuses often map to UNKNOWN at the high-level status.
                if (primalFeasible) {
                    retState = Optimisation.State.FEASIBLE;
                } else if (mySolver.isDualFeasible()) {
                    retState = Optimisation.State.VALID;
                } else {
                    retState = Optimisation.State.UNEXPLORED;
                }
            }

        } catch (IloException cause) {
            BasicLogger.error("CPLEX solve failed: {}", cause.getMessage());
            retValue = Double.NaN;
            retState = Optimisation.State.FAILED;
            LAST_BEST_BOUND.set(Double.NaN);
        }

        return Optimisation.Result.of(retValue, retState, retSolution);
    }

    private double readBestBound() throws IloException {
        double bestBound = mySolver.getBestObjValue();
        if (Double.isFinite(bestBound)) {
            return bestBound;
        }
        return Double.NaN;
    }
}
