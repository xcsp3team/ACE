/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics.variables.dynamic;

import java.util.Arrays;

import constraints.Constraint;
import heuristics.variables.HeuristicVariablesDynamic;
import interfaces.ObserverPropagation;
import interfaces.ObserverRuns;
import interfaces.TagMaximize;
import search.backtrack.SolverBacktrack;
import utility.Enums.EWeighting;
import utility.sets.SetDense;
import variables.Variable;
import variables.domains.Domain;

public abstract class HeuristicVariablesConflictBased extends HeuristicVariablesDynamic implements ObserverRuns, ObserverPropagation, TagMaximize {

	private int time; // corresponds to the number of times a wipe-out occurred
	private int[] ctime; // ctime[i] corresponds to the last time a wipe-out occurred for constraint i

	public double[] vscores; // the score of all variables
	public double[] cscores; // the score of constraints (mainly used for CHS)

	double[][] cvscores;

	final double SMOOTHING = 0.995;
	final double ALPHA0 = 0.1, ALPHA_LIMIT = 0.06, ALPHA_DECREMENT = 0.000001; // for CHS
	double alpha; // for CHS

	@Override
	public void reset() {
		time = 0;
		Arrays.fill(ctime, 0);
		Arrays.fill(vscores, 0);
		Arrays.fill(cscores, 0);
		for (double[] t : cvscores)
			Arrays.fill(t, 0);
	}

	@Override
	public void beforeRun() {
		if (solver.restarter.numRun > 0 && solver.restarter.numRun % solver.rs.cp.settingRestarts.dataResetPeriod == 0)
			reset();
		alpha = ALPHA0;
		if (settings.weighting == EWeighting.CHS) { // smoothing
			for (int i = 0; i < cscores.length; i++)
				cscores[i] *= (Math.pow(SMOOTHING, time - ctime[i]));
		}
	}

	@Override
	public void afterAssignment(Variable x, int a) {
		if (settings.weighting != EWeighting.VAR && settings.weighting != EWeighting.CHS)
			for (Constraint c : x.ctrs)
				if (c.futvars.size() == 1) {
					int y = c.futvars.dense[0]; // the other variable whose score must be updated
					vscores[c.scp[y].num] -= cvscores[c.num][y];
				}
	}

	@Override
	public void afterUnassignment(Variable x) {
		if (settings.weighting != EWeighting.VAR && settings.weighting != EWeighting.CHS)
			for (Constraint c : x.ctrs)
				if (c.futvars.size() == 2) { // since a variable has just been unassigned, it means that there was only one future variable
					int y = c.futvars.dense[0]; // the other variable whose score must be updated
					vscores[c.scp[y].num] += cvscores[c.num][y];
				}
	}

	@Override
	public void whenWipeout(Constraint c, Variable x) {
		time++;
		if (settings.weighting == EWeighting.VAR)
			vscores[x.num]++;
		else if (c != null) {
			if (settings.weighting == EWeighting.CHS) {
				double r = 1.0 / (time - ctime[c.num]);
				double increment = alpha * (r - cscores[c.num]);
				cscores[c.num] += increment;
				// SetDense futvars = c.futvars;
				// for (int i = futvars.limit; i >= 0; i--) {
				// Variable y = c.scp[futvars.dense[i]];
				// vscores[y.num] += increment;
				// cvscores[c.num][futvars.dense[i]] += increment;
				// }

				// cscores[c.num] = (1 - alpha) * cscores[c.num] + alpha * (1.0 / (time - ctime[c.num]));
				alpha = Double.max(ALPHA_LIMIT, alpha - ALPHA_DECREMENT);
			} else {
				double increment = 1;
				cscores[c.num] += increment; // just +1 in that case (can be useful for other objects, but not directly for wdeg)
				SetDense futvars = c.futvars;
				for (int i = futvars.limit; i >= 0; i--) {
					Variable y = c.scp[futvars.dense[i]];
					if (settings.weighting == EWeighting.CACD) { // in this case, the increment is not 1 as for UNIT
						Domain dom = y.dom;
						boolean test = false; // hard coding ; this variant does not seem to be interesting
						if (test) {
							int depth = solver.depth();
							int nRemoved = 0;
							for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a)) {
								if (dom.getRemovedLevelOf(a) != depth)
									break;
								nRemoved++;
							}
							increment = 1.0 / (futvars.size() * (dom.size() + nRemoved));
						} else
							increment = 1.0 / (futvars.size() * (dom.size() == 0 ? 0.5 : dom.size()));
					}
					vscores[y.num] += increment;
					cvscores[c.num][futvars.dense[i]] += increment;
				}
			}
		}
		ctime[c.num] = time;
		// if (cnt++ % 100 == 0) {
		// System.out.println("fff " + pb.rs.cp.varh.weighting + " " + increment);
		// for (Variable x : pb.variables) System.out.print(x.wdeg + " ");
		// System.out.println(); }
	}

	@Override
	public void whenReduction(Constraint c, Variable x) {}

	public HeuristicVariablesConflictBased(SolverBacktrack solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
		this.ctime = new int[solver.pb.constraints.length];
		this.vscores = new double[solver.pb.variables.length];
		this.cscores = new double[solver.pb.constraints.length];
		this.cvscores = new double[solver.pb.constraints.length][0];
		for (int i = 0; i < cvscores.length; i++)
			this.cvscores[i] = new double[solver.pb.constraints[i].scp.length];
	}

}

// private WeigthClustering wc;

// private class WeigthClustering extends KMeansClustering {
//
// @Override
// public int nValues() {
// return solver.pb.variables.length;
// }
//
// @Override
// public double value(int i) {
// return solver.pb.variables[i].wdeg;
// }
// }

// @Override
// public void beforeRun() {
// if (solver.rs.cp.restarting.hMeasureResetPeriod == 0) {
// wc = wc == null ? new WeigthClustering() : wc;
// int weight = wc.recluster();
// for (Variable x : solver.pb.variables)
// x.wdeg = x.wdeg <= weight ? 0 : weight;
// } else
// if (solver.restarter.numRun % solver.rs.cp.restarting.dataResetPeriod == 0)
// solver.pb.resetWdeg();
// }