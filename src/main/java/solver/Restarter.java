/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package solver;

import static utility.Kit.control;

import java.util.function.Supplier;

import constraints.global.Extremum.ExtremumCst.MaximumCst.MaximumCstLE;
import dashboard.Control.OptionsRestarts;
import interfaces.Observers.ObserverOnRuns;
import optimization.ObjectiveVariable;
import optimization.Optimizer;
import sets.SetDense;
import utility.Kit;
import variables.Variable;

/**
 * A restarter is used by a solver in order to manage restarts (successive runs restarting from the root node).
 * 
 * @author Christophe Lecoutre
 */
public class Restarter implements ObserverOnRuns {

	/**
	 * Builds and returns a restarter object to be attached to the specified solver
	 * 
	 * @param solver
	 *            The solver to which the restarter object must be attached
	 * @return a restarter object to be attached to the specified solver
	 */
	public static Restarter buildFor(Solver solver) {
		return solver.head.control.lns.enabled ? new RestarterLNS(solver) : new Restarter(solver);
	}

	/**
	 * Different criteria to be used as measures for restarts
	 */
	public static enum RestartMeasure {
		FAILED, WRONG, BACKTRACK, SOLUTION;
	}

	/**********************************************************************************************
	 * Implementing interfaces
	 *********************************************************************************************/

	private long lubyCutoffFor(long i) {
		int k = (int) Math.floor(Math.log(i) / Math.log(2)) + 1;
		long pow = (long) Math.pow(2, k - 1);
		return i == pow * 2 - 1 ? pow : lubyCutoffFor(i - pow + 1);
	}

	@Override
	public void beforeRun() {
		numRun++;
		if ((numRun - solver.solutions.lastRun) % options.resetPeriod == 0) {
			nRestartsSinceReset = 0;
			baseCutoff = baseCutoff * options.resetCoefficient;
			Kit.log.config("    ...resetting restart cutoff to " + baseCutoff);
		}
		if (solver.propagation.runPossiblyAtRoot()) // if propagation has been run
			nRestartsSinceReset = 0;
		if (currCutoff != Long.MAX_VALUE) {
			long offset = options.luby ? lubyCutoffFor(nRestartsSinceReset + (long) 1) * 150
					: (long) (baseCutoff * Math.pow(options.factor, nRestartsSinceReset));
			currCutoff = measureSupplier.get() + offset;
		}
		nRestartsSinceReset++;
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	/**
	 * The solver to which the restarter is attached.
	 */
	public Solver solver;

	/**
	 * The options for piloting the restarter (redundant field).
	 */
	private OptionsRestarts options;

	/**
	 * The measure function used for handling cutoff values
	 */
	public final Supplier<Long> measureSupplier;

	/**
	 * The number of the current run;
	 */
	public int numRun = -1;

	/**
	 * The base cutoff, as initially specified.
	 */
	private long baseCutoff;

	/**
	 * The current value of the cutoff (note that this value can evolve between successive runs).
	 */
	public long currCutoff;

	/**
	 * Records the number of restarts made since the last call to the method reset
	 */
	private int nRestartsSinceReset;

	/**
	 * Resets the object. This is usually not used.
	 */
	public final void reset() {
		numRun = -1;
		currCutoff = baseCutoff = options.cutoff;
		nRestartsSinceReset = 0;
	}

	/**
	 * Returns the method (supplier) to be used for computing the current measure
	 * 
	 * @return the method (supplier) to be used for computing the current measure
	 */
	private Supplier<Long> measureSupplier() {
		Solver sb = solver != null ? solver : null;
		switch (options.measure) {
		case FAILED:
			return () -> sb.stats.nFailedAssignments;
		case WRONG:
			return () -> sb.stats.nWrongDecisions;
		case BACKTRACK:
			return () -> sb.stats.nBacktracks;
		case SOLUTION:
			return () -> solver.solutions.found;
		default:
			throw new AssertionError();
		}
	}

	/**
	 * Builds a restarter object to be used with the specified solver
	 * 
	 * @param solver
	 *            the solver to which the restarter is attached
	 */
	public Restarter(Solver solver) {
		this.solver = solver;
		// this.cop = solver.head.control.general.framework == TypeFramework.COP;
		this.options = solver.head.control.restarts;
		if (solver.problem.optimizer != null && options.cutoff < Integer.MAX_VALUE)
			options.cutoff *= 10; // For COPs, the cutoff value is multiplied by 10; hard coding
		this.measureSupplier = measureSupplier();
		currCutoff = baseCutoff = options.cutoff; // reset();
	}

	private long cnt;

	/**
	 * Returns true if the current run is considered as being finished
	 * 
	 * @return true if the current run is considered as being finished
	 */
	public boolean currRunFinished() {
		Optimizer optimizer = solver.problem.optimizer;
		if (optimizer != null && ((cnt++) % 5) == 0) // code for portfolio mode; hard coding
			optimizer.possiblyUpdateLocalBounds();
		if (measureSupplier.get() >= currCutoff)
			return true;
		if (optimizer == null || numRun != solver.solutions.lastRun)
			return false;
		return options.restartAfterSolution || optimizer.ctr instanceof MaximumCstLE || optimizer.ctr instanceof ObjectiveVariable;
	}

	/**
	 * Returns true if no more run must be started
	 * 
	 * @return true if no more run must be started
	 */
	public boolean allRunsFinished() {
		return numRun + 1 >= options.nRuns;
	}

	/**********************************************************************************************
	 * TO BE FINALIZED: Subclasses for LNS
	 *********************************************************************************************/

	public final static class RestarterLNS extends Restarter {

		/**
		 * Limit of exploration (if the number of past variables is smaller, then we must stop)
		 */
		private int explorationLimit;

		@Override
		public void beforeRun() {
			super.beforeRun();
			int[] solution = solver.solutions.last;
			if (solution == null)
				return;
			heuristic.freezeVariables(solution);
			for (int i = heuristic.fragment.limit; i >= 0; i--) {
				Variable x = solver.problem.variables[heuristic.fragment.dense[i]];
				int a = solution[x.num];
				if (x.dom.contains(a)) { // because the objective constraint may change, this test must be done
					solver.assign(x, a);
					if (solver.propagation.runAfterAssignment(x) == false) {
						solver.backtrack(x);
						break;
					}
				}
			}
			explorationLimit = solver.futVars.nPast();
		}

		@Override
		public boolean currRunFinished() {
			return super.currRunFinished() || solver.futVars.nPast() < explorationLimit;
		}

		@Override
		public void afterRun() {
			solver.backtrackToTheRoot(); // because see Method doRun in Solver
		}

		/**
		 * The heuristic to be used for freezing variables in LNS
		 */
		private final HeuristicFreezing heuristic;

		public RestarterLNS(Solver solver) {
			super(solver);
			this.heuristic = HeuristicFreezing.buildFor(this);
		}

		// ************************************************************************
		// ***** Freezing heuristics
		// ************************************************************************

		public static abstract class HeuristicFreezing {

			public static HeuristicFreezing buildFor(RestarterLNS restarter) {
				if (restarter.solver.head.control.lns.clazz.equals("Impact"))
					return new Impact(restarter);
				return new Rand(restarter);
			}

			protected final RestarterLNS restarter;

			public final SetDense fragment;

			public HeuristicFreezing(RestarterLNS restarter) {
				this.restarter = restarter;
				int n = restarter.solver.problem.variables.length;
				int nf = restarter.solver.head.control.lns.nFreeze, pf = restarter.solver.head.control.lns.pFreeze;
				this.fragment = new SetDense(n);
				int fragmentSize = 0 < nf && nf < n ? nf : 0 < pf && pf < 100 ? 1 + (pf * n) / 100 : -1;
				control(0 < fragmentSize && fragmentSize < n, () -> "You must specify the number or percentage of variables to freeze for LNS");
				this.fragment.limit = fragmentSize - 1;
			}

			public abstract void freezeVariables(int[] solution);

			public static final class Impact extends HeuristicFreezing {
				// TO BE FINALIZED (note sure that it is correct/coherent)

				private final Variable[] variables;

				private int[] before, after;

				public Impact(RestarterLNS restarter) {
					super(restarter);
					this.variables = restarter.solver.problem.variables;
					this.before = new int[variables.length];
					this.after = new int[variables.length];

				}

				private void storeDomainSizes(int[] t) {
					for (int i = 0; i < variables.length; i++)
						t[i] = variables[i].dom.size();
				}

				@Override
				public void freezeVariables(int[] solution) {
					int[] dense = fragment.dense;
					Kit.shuffle(dense, restarter.solver.head.random);
					Integer bestImpacted = null;
					for (int i = 0; i < fragment.size(); i++) {
						if (bestImpacted != null) {
							int tmp = dense[bestImpacted];
							dense[bestImpacted] = dense[i];
							dense[i] = tmp;
						}
						// else we automatically add the first element of shuffled (at position size)
						restarter.solver.assign(variables[dense[i]], solution[dense[i]]);

						storeDomainSizes(before);
						restarter.solver.propagation.runInitially();
						storeDomainSizes(after);

						bestImpacted = null;
						int bestImpact = 0;
						for (int j = i + 1; j < dense.length; j++) {
							int impact = before[dense[j]] - after[dense[j]];
							if (impact > bestImpact) {
								bestImpacted = j;
								bestImpact = impact;
							}
						}
					}
					restarter.solver.backtrackToTheRoot();
				}
			}

			public static final class Rand extends HeuristicFreezing {

				public Rand(RestarterLNS restarter) {
					super(restarter);
				}

				@Override
				public void freezeVariables(int[] solution) {
					Kit.shuffle(fragment.dense, restarter.solver.head.random);
				}
			}
		}
	}
}
