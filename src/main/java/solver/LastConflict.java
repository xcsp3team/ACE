package solver;

import java.util.stream.Collectors;
import java.util.stream.IntStream;

import interfaces.Observers.ObserverDecisions;
import interfaces.Observers.ObserverRuns;
import utility.Kit;
import variables.Variable;

/**
 * This object implements last-conflict reasoning (lc). <br />
 * See Reasoning from last conflict(s) in constraint programming. Artif. Intell. 173(18): 1592-1614 (2009) by C. Lecoutre, L. Sais, S. Tabary, and V. Vidal:
 * 
 * @author Christophe Lecoutre
 */
public final class LastConflict implements ObserverRuns, ObserverDecisions {

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

	private Solver solver;

	private int k; // k is the parameter of lc (necessarily > 0)

	private Variable[] vars; // recorded variables when reasoning with lc

	private int nVars; // number of recorded variables

	private Variable lastAssigned;

	private Variable candidate; // candidate for last reasoning

	private Statistics statistics;

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

	public LastConflict(Solver solver, int k) {
		this.solver = solver;
		this.k = k;
		this.vars = new Variable[k];
		this.statistics = new Statistics(k);
		Kit.control(k > 0);
	}

	public Variable lastConflictPriorityVar() {
		// entering last reasoning mode?
		if (nVars == 0) {
			if (lastAssigned == null || lastAssigned.assigned())
				return null;
			statistics.startLevel = solver.depth() + 1;
			vars[nVars++] = lastAssigned;
			return lastAssigned;
		}
		// using one of the recorded variables?
		for (int i = 0; i < nVars; i++)
			if (!vars[i].assigned())
				return vars[i];
		// leaving last reasoning mode?
		if (nVars == k || candidate == null || candidate.assigned()) {
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

	@Override
	public final void beforePositiveDecision(Variable x, int a) {
		if (nVars == 0)
			lastAssigned = x;
	}

	@Override
	public void beforeNegativeDecision(Variable x, int a) {
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
	}
}
