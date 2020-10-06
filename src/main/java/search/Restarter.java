/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search;

import java.util.function.Supplier;

import org.xcsp.common.Types.TypeFramework;

import constraints.hard.global.Extremum.ExtremumCst.MaximumCst.MaximumCstLE;
import constraints.hard.global.ObjVar;
import dashboard.ControlPanel.Restarting;
import interfaces.ObserverRuns;
import search.backtrack.SolverBacktrack;
import utility.Enums.EStopping;
import utility.Kit;
import utility.exceptions.UnreachableCodeException;

/**
 * A restarter is used by a solver in order to manage restarts (successive runs from the root node).
 */
public class Restarter implements ObserverRuns {

	private long lubyCutoffFor(long i) {
		int k = (int) Math.floor(Math.log(i) / Math.log(2)) + 1;
		long pow = (long) Math.pow(2, k - 1);
		return i == pow * 2 - 1 ? pow : lubyCutoffFor(i - pow + 1);
	}

	@Override
	public void beforeRun() {
		numRun++;
		nRestartsSinceLastReset++;
		if (nRestartsSinceLastReset == setting.nRestartsResetPeriod) {
			nRestartsSinceLastReset = 0;
			baseCutoff = baseCutoff * setting.nRestartsResetCoefficient;
			Kit.log.info("BaseCutoff reset to " + baseCutoff);
		}
		if (currCutoff != Long.MAX_VALUE) {
			long offset = setting.luby ? lubyCutoffFor(numRun + 1) * 100 : (long) (baseCutoff * Math.pow(setting.factor, nRestartsSinceLastReset));
			currCutoff = measureSupplier.get() + offset;
		}
		// boolean b = forceRootPropagation;
		// if (!b && solver.rs.cp.framework == TypeFramework.COP)
		// b = numRun - 1 == solver.solManager.lastSolutionRun; // || !(solver.pb.optimizationPilot instanceof OptimizationPilotDecreasing);
		if (forceRootPropagation || (solver.rs.cp.framework == TypeFramework.COP && numRun - 1 == solver.solManager.lastSolutionRun)) {
			forceRootPropagation = false;
			nRestartsSinceLastReset = 0;
			if (solver.propagation.runInitially() == false)
				solver.stoppingType = EStopping.FULL_EXPLORATION;
		}
	}

	@Override
	public void afterRun() {
		if (solver.rs.cp.framework == TypeFramework.COP)
			solver.pb.optimizationPilot.afterRun();
	}

	/**
	 * The solver to which the restarter is attached.
	 */
	public Solver solver;

	/**
	 * The settings used for piloting the restarter (redundant field).
	 */
	private Restarting setting;

	/**
	 * The measure used for handling cutoff values.
	 */
	public final Supplier<Long> measureSupplier;

	/**
	 * The number of the current run;
	 */
	public int numRun = -1;

	/**
	 * The base cutoff, and the current cutoff value as this value can evolve between successive runs.
	 */
	public long baseCutoff, currCutoff;

	private int nRestartsSinceLastReset = -1;

	/**
	 * Set to true when running propagation from scratch at the root node must be made when a restart occurs.
	 */
	public boolean forceRootPropagation;

	public void reset() {
		numRun = -1;
		currCutoff = baseCutoff = setting.cutoff;
		nRestartsSinceLastReset = -1;
	}

	private Supplier<Long> measureSupplier() {
		SolverBacktrack sb = solver instanceof SolverBacktrack ? ((SolverBacktrack) solver) : null;
		switch (setting.measure) {
		case FAILED:
			return () -> sb.backtrackStatistics.nFailedAssignments;
		case WRONG:
			return () -> sb.backtrackStatistics.nWrongDecisions;
		case BACKTRACK:
			return () -> sb.backtrackStatistics.nBacktracks;
		case MAX_DEPTH:
			return () -> (long) sb.maxDepth;
		case SOLUTION:
			return () -> solver.solManager.nSolutionsFound;
		default:
			throw new UnreachableCodeException();
		}
	}

	public Restarter(Solver solver) {
		this.solver = solver;
		this.setting = solver.rs.cp.restarting;
		this.measureSupplier = measureSupplier();
		if (solver.rs.cp.framework == TypeFramework.COP)
			setting.cutoff *= 10;
		reset();
	}

	private long cnt;

	public boolean currRunFinished() {
		if (solver.pb.optimizationPilot != null && ((cnt++) % 5) == 0)
			solver.pb.optimizationPilot.possiblyUpdateLocalBounds();
		if (measureSupplier.get() >= currCutoff)
			return true;
		if (solver.rs.cp.framework != TypeFramework.COP || numRun != solver.solManager.lastSolutionRun)
			return false;
		if (setting.restartAfterSolution)
			return true;
		if (solver.pb.optimizationPilot.ctr instanceof MaximumCstLE || solver.pb.optimizationPilot.ctr instanceof ObjVar)
			return true;
		return false;
	}

	/**
	 * Determines if there are no more (re)starts to perform.
	 */
	public boolean allRunsFinished() {
		return numRun + 1 >= setting.nRunsLimit;
	}
}
