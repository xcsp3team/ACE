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

import dashboard.Control.OptionsRestarts;
import dashboard.Input;
import heuristics.HeuristicVariables;
import heuristics.HeuristicVariablesDynamic;
import heuristics.HeuristicVariablesDynamic.Freezer;
import heuristics.HeuristicVariablesDynamic.RunRobin;
import interfaces.Observers.ObserverOnRuns;
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
		localStats.atStart();
		if (solver.head.control.valh.solutionSavingStart != -1) {
			if (solver.solutions.found == 0)
				solver.head.control.valh.solutionSavingStart++;
			else if (solver.head.control.valh.solutionSavingStart == numRun)
				Kit.log.config("\tStarting SOS");
		}
		if (numRun > 0 && numRun % options.resetPeriod == 0) {
			// if ((numRun - solver.solutions.lastRun) % options.resetPeriod == 0) {
			nRestartsSinceReset = 0;
			baseCutoff = baseCutoff + 5; // * options.resetCoefficient;
			Kit.log.config(Kit.Color.YELLOW.coloring(" ...resetting") + " restart cutoff to " + baseCutoff);
		}
		if (solver.propagation.runPossiblyAtRoot()) // if propagation has been run
			nRestartsSinceReset = 0;
		if (currCutoff != Long.MAX_VALUE) {
			long offset = options.luby ? lubyCutoffFor(nRestartsSinceReset + (long) 1) * 150
					: (long) (baseCutoff * Math.pow(options.factor, nRestartsSinceReset));
			currCutoff = measureSupplier.get() + offset;
		}
		nRestartsSinceReset++;

		if (solver.head.control.varh.arrayPriorityRunRobin) {
			// TODO control that aprr is not used with pr1 or pr2
			int k = solver.problem.varArrays.length;
			// for (VarArray va : solver.problem.arrays) System.out.println("hhhh " + Kit.join(va.flatVars));
			int index = numRun % (k + 1);
			if (index == 0)
				solver.heuristic.resetPriorityVars();
			else
				solver.heuristic.setPriorityVars((Variable[]) solver.problem.varArrays[index - 1].flatVars, 0);
		}

		if (solver.head.control.varh.secondScored) {
			solver.heuristic.bestScoredVariable.cleanStack();
			if (solver.heuristic instanceof RunRobin) {
				for (HeuristicVariables h : ((RunRobin) solver.heuristic).pool)
					h.bestScoredVariable.cleanStack();
			}
		}
	}

	@Override
	public void afterRun() {
		localStats.atEnd();
		// System.out.println(localStats);
	}

	class LocalStats {

		public long nFoundSolutionAtRunStart;

		public long boundAtRunStart = -1;

		public long measureAtRunStart;

		/**
		 * nFoundSolutions[i] is the number of solutions found by run i
		 */
		long[] nFoundSolutions;

		/**
		 * gains[i] is the gain (bound improvement) obtained at run i
		 */
		long[] gains;

		/**
		 * lengths[i] is the length (measure as the number of failed assignments) of run i
		 */
		long[] lengths;

		/**
		 * heuristics[i] is the heuristic used at run i
		 */
		HeuristicVariables[] heuristics;

		private LocalStats(int size) {
			this.nFoundSolutions = new long[size];
			this.gains = solver.problem.optimizer != null ? new long[size] : null;
			this.lengths = new long[size];
			this.heuristics = new HeuristicVariables[size];
		}

		private void atStart() {
			nFoundSolutionAtRunStart = solver.solutions.found;
			if (gains != null)
				boundAtRunStart = solver.solutions.bestBound;
			measureAtRunStart = measureSupplier.get();
		}

		private void atEnd() {
			if (numRun >= nFoundSolutions.length)
				return;
			nFoundSolutions[numRun] = solver.solutions.found - nFoundSolutionAtRunStart;
			if (gains != null) {
				boolean firstSolutions = nFoundSolutionAtRunStart == 0 && solver.solutions.found > 0;
				long l = (firstSolutions ? solver.solutions.firstBound : boundAtRunStart);
				gains[numRun] = Math.abs(solver.solutions.bestBound - (firstSolutions ? solver.solutions.firstBound : boundAtRunStart))
						+ (firstSolutions ? 1 : 0); // bonus de 1 ? other ?
			}
			lengths[numRun] = measureSupplier.get() - measureAtRunStart;
			heuristics[numRun] = solver.heuristic instanceof RunRobin ? ((RunRobin) solver.heuristic).current : solver.heuristic;
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder("  Restart Stats:\n");
			for (int i = 0; i <= numRun; i++)
				sb.append("\t" + nFoundSolutions[i] + (gains != null ? " " + gains[i] : "") + " " + lengths[i] + " " + heuristics[i].getClass().getSimpleName()
						+ "\n");
			return sb.toString();
		}
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

	public LocalStats localStats;
	
	
	public Freezer freezer;

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
		case SOLUTION: // TODO: pb with CSP, as several similar solutions may be found
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
		this.localStats = new LocalStats(2000); // TODO: hard coding
	}

	private long cnt;

	/**
	 * Returns true if the current run is considered as being finished
	 * 
	 * @return true if the current run is considered as being finished
	 */
	public boolean currRunFinished() {
		Optimizer optimizer = solver.problem.optimizer;
		if (Input.portfolio && optimizer != null && ((cnt++) % 5) == 0) // code for portfolio mode; hard coding
			optimizer.possiblyUpdateLocalBounds();
		long measure = measureSupplier.get();
		if (measure >= currCutoff)
			return true;
		if (optimizer != null && solver.solutions.found - localStats.nFoundSolutionAtRunStart > options.solRunLimit)
			// for CSP, may be a problem
			return true;
		if (freezer != null && !freezer.isCurrentlyFrozen()) {
			if (2 * measure >= currCutoff)
				freezer.freezeAt(numRun);
		}
		if (optimizer == null || numRun != solver.solutions.lastRun)
			return false;
		return options.restartAfterSolution;
		// for CSP, shouldnt'we add the last solution as nogood if restartAfterSolution (otherwise, possibility of
		// finding it several times?)?
	}

	/**
	 * Returns true if no more run must be started
	 * 
	 * @return true if no more run must be started
	 */
	public boolean allRunsFinished() {
		return numRun + 1 >= options.nRuns;
	}

	public int howManyRunsSincelastSolution() {
		int v = solver.solutions.lastRun;
		return v == -1 ? -1 : (numRun - v);
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
