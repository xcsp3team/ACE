/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package solver;

import static java.util.stream.Collectors.joining;
import static utility.Kit.control;

import java.util.stream.IntStream;

import dashboard.Output;
import interfaces.Observers.ObserverOnDecisions;
import interfaces.Observers.ObserverOnRuns;
import utility.Kit;
import variables.Variable;

/**
 * This object implements last-conflict reasoning (lc). See "Reasoning from last conflict(s) in constraint programming". Artif. Intell. 173(18): 1592-1614
 * (2009) by C. Lecoutre, L. Sais, S. Tabary, and V. Vidal.
 * 
 * @author Christophe Lecoutre
 */
public final class LastConflict implements ObserverOnRuns, ObserverOnDecisions {

	/**********************************************************************************************
	 * Implementing interfaces
	 *********************************************************************************************/

	@Override
	public void beforeRun() {
		storeSize = 0;
		lastAssigned = null;
		candidate = null;
	}

	@Override
	public void afterRun() {
		statistics.display();
	}

	@Override
	public final void beforePositiveDecision(Variable x, int a) {
		if (storeSize == 0)
			lastAssigned = x;
	}

	@Override
	public void beforeNegativeDecision(Variable x, int a) {
		// is x the candidate for next insertion (after potentially lastAssigned)?
		if (storeSize == 0) {
			if (x != lastAssigned)
				candidate = x;
		} else if (storeSize < k) {
			for (int i = 0; i < storeSize; i++)
				if (store[i] == x)
					return;
			candidate = x;
		}
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	/**
	 * The solver to which lc is attached
	 */
	private Solver solver;

	/**
	 * The main parameter of lc: the maximum number of variables that can be recorded when reasoning with lc.
	 */
	private int k;

	/**
	 * The recorded variables, at indexes from 0 to storeSize (excluded)
	 */
	private Variable[] store;

	/**
	 * The number of recorded variables, to be used when reasoning with lc
	 */
	private int storeSize;

	/**
	 * The last variable explicitly assigned by the solver
	 */
	private Variable lastAssigned;

	/**
	 * Candidate for last reasoning
	 */
	private Variable candidate;

	/**
	 * The object used to record some statistics about the behavior of lc
	 */
	private Statistics statistics;

	/**
	 * The intern class used to record some statistics about lc
	 */
	private class Statistics {
		private int startLevel;

		/**
		 * cnts[i] is the number of times we stop reasoning at level i
		 */
		private int[] cnts;

		/**
		 * jmps[i] is the cumulated jump sizes when we stop reasoning at level i
		 */
		private int[] jmps;

		private Statistics(int k) {
			cnts = new int[k + 1];
			jmps = new int[k + 1];
		}

		private void update(int offset) {
			cnts[storeSize]++;
			jmps[storeSize] += (startLevel - solver.depth() + offset);
		}

		private void display() {
			if (storeSize > 0)
				update(0); // last update to be done since not taken into account when backtracking to level 0
			Kit.log.info(() -> "last-conflicts  " + IntStream.range(1, k + 1)
					.mapToObj(i -> i + ":(#=" + cnts[i] + (cnts[i] == 0 ? "" : ",avg=" + Output.decimalFormat.format(jmps[i] / (double) cnts[i])))
					.collect(joining(")  ")) + ")\n");
		}
	}

	/**
	 * Builds an object implementing last-conflict reasoning (lc)
	 * 
	 * @param solver
	 *            the solver to which lc is attached
	 * @param k
	 *            the level (maximum number of variables that can enter the store of lc) of lc
	 */
	public LastConflict(Solver solver, int k) {
		this.solver = solver;
		this.k = k;
		this.store = new Variable[k];
		this.statistics = new Statistics(k);
		control(k > 0);
	}

	/**
	 * Returns the variable identified as priority by lc, or null
	 * 
	 * @return the variable identified as priority by lc, or null
	 */
	public Variable priorityVariable() {
		// entering last reasoning mode?
		if (storeSize == 0) {
			if (lastAssigned == null || lastAssigned.assigned())
				return null;
			statistics.startLevel = solver.depth() + 1;
			store[storeSize++] = lastAssigned;
			return lastAssigned;
		}
		// using one of the recorded variables?
		for (int i = 0; i < storeSize; i++)
			if (!store[i].assigned())
				return store[i];
		// leaving last reasoning mode?
		if (storeSize == k || candidate == null || candidate.assigned()) {
			statistics.update(storeSize);
			storeSize = 0;
			candidate = null;
			return null;
		}
		// recording the candidate
		store[storeSize++] = candidate;
		candidate = null;
		return store[storeSize - 1];
	}

}
