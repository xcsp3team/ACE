/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search.backtrack;

import java.util.stream.Collectors;
import java.util.stream.IntStream;

import interfaces.ObserverRuns;
import utility.Kit;
import variables.Variable;

public final class LastConflictReasoner implements ObserverRuns {

	@Override
	public void beforeRun() {
		nVars = 0;
		candidate = null;
	}

	@Override
	public void afterRun() {
		if (k > 0)
			statistics.display();
	}

	private SolverBacktrack solver;

	private int k; // k is the parameter of lc (0 if inactive)

	private Variable[] vars; // recorded variables when reasoning with lc

	private int nVars; // number of recorded variables

	private Variable lastAssigned;

	private Variable candidate; // candidate for last reasoning

	private Statistics statistics;

	// private int[] progressSaving;

	private class Statistics {
		private int startLevel;
		private int[] cnts; // cnts[i] is the number of times we stop reasoning at level i
		private int[] jmps; // jmps[i] is the cumulated jump sizes when we stop reasoning at level i

		private Statistics(int k) {
			cnts = new int[k + 1];
			jmps = new int[k + 1];
		}

		private void update(int offset) {
			cnts[nVars]++;
			jmps[nVars] += (startLevel - solver.depth() + offset);
		}

		public void display() {
			if (nVars > 0)
				update(0); // last update to be done since not taken into account when backtracking to level 0
			String s = IntStream.range(1, cnts.length)
					.mapToObj(i -> i + ":(#=" + cnts[i] + (cnts[i] == 0 ? "" : ",avg=" + Kit.decimalFormat.format(jmps[i] / (double) cnts[i])))
					.collect(Collectors.joining(")  "));
			Kit.log.info("last-conflicts  " + s + ")\n");
		}
	}

	public LastConflictReasoner(SolverBacktrack solver, int k) {
		this.solver = solver;
		this.k = k;
		this.vars = new Variable[k];
		this.statistics = new Statistics(k);
		// progressSaving = Kit.repeat(-1, solver.problem.variables.length);
	}

	public Variable lastConflictPriorityVar() {
		if (k == 0)
			return null;
		// entering last reasoning mode?
		if (nVars == 0) {
			if (lastAssigned == null || lastAssigned.isAssigned())
				return null;
			// Arrays.fill(progressSaving, -1);
			statistics.startLevel = solver.depth() + 1;
			vars[nVars++] = lastAssigned;
			return lastAssigned;
		}
		// using one of the recorded variables?
		for (int i = 0; i < nVars; i++)
			if (!vars[i].isAssigned())
				return vars[i];
		// leaving last reasoning mode?
		if (nVars == k || candidate == null || candidate.isAssigned()) {
			statistics.update(nVars);
			nVars = 0;
			candidate = null;
			return null;
		}
		// recording the candidate
		vars[nVars++] = candidate;
		candidate = null;
		return vars[nVars - 1];
	}

	public final void onAssignment(Variable x) {
		if (k > 0 && nVars == 0)
			lastAssigned = x;
	}

	public void onRefutation(Variable x, int a) {
		if (k == 0)
			return;
		// is variable the candidate for next insertion (after potentially lastAssigned)
		if (nVars == 0) {
			if (x != lastAssigned)
				candidate = x;
		} else if (nVars < k) {
			for (int i = 0; i < nVars; i++)
				if (vars[i] == x)
					return;
			candidate = x;
		}
		// if (nVars == 1 && x != vars[0]) progressSaving[x.num] = a;
	}

}
