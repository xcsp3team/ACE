package solver;

import static dashboard.Output.BOUND;
import static dashboard.Output.BOUNDS;
import static dashboard.Output.BOUND_CPU;
import static dashboard.Output.BOUND_WCK;
import static dashboard.Output.CPU;
import static dashboard.Output.DEPTHS;
import static dashboard.Output.GLOBAL;
import static dashboard.Output.GUARANTEED_GAC;
import static dashboard.Output.MAP_SIZE;
import static dashboard.Output.MEM;
import static dashboard.Output.N_ADDED_CTRS;
import static dashboard.Output.N_BACKTRACKS;
import static dashboard.Output.N_BUILT_BRANCHES;
import static dashboard.Output.N_DECISIONS;
import static dashboard.Output.N_DELIMINABLES;
import static dashboard.Output.N_EFFECTIVE;
import static dashboard.Output.N_EFFECTIVE_SINGLETON_TESTS;
import static dashboard.Output.N_FAILED;
import static dashboard.Output.N_FOUND_SINGLETONS;
import static dashboard.Output.N_IELIMINABLES;
import static dashboard.Output.N_INFERENCES;
import static dashboard.Output.N_NOGOODS;
import static dashboard.Output.N_PELIMINABLES;
import static dashboard.Output.N_RELIMINABLES;
import static dashboard.Output.N_REMOVED_TUPLES;
import static dashboard.Output.N_SELIMINABLES;
import static dashboard.Output.N_SINGLETON_TESTS;
import static dashboard.Output.N_TOO_LARGE_KEYS;
import static dashboard.Output.N_VALUES;
import static dashboard.Output.N_WRONG;
import static dashboard.Output.PREPROCESSING;
import static dashboard.Output.REMOVED_BY_AC;
import static dashboard.Output.REVISIONS;
import static dashboard.Output.RUN;
import static dashboard.Output.SOL1_CPU;
import static dashboard.Output.SOLS;
import static dashboard.Output.SOLVER;
import static dashboard.Output.STOP;
import static dashboard.Output.SUM_BRANCH_SIZES;
import static dashboard.Output.UNSAT;
import static dashboard.Output.WCK;

import java.text.NumberFormat;

import org.xcsp.common.Types.TypeFramework;

import interfaces.Observers.ObserverDecisions;
import interfaces.Observers.ObserverRuns;
import interfaces.Observers.ObserverSearch;
import learning.IpsRecorderForEquivalence;
import learning.ReductionOperator;
import problem.Features.Attributes;
import propagation.Forward;
import propagation.GAC;
import propagation.SAC;
import propagation.SAC.SACGreedy;
import utility.Enums.EStopping;
import utility.Kit;
import utility.Kit.Stopwatch;
import variables.Variable;

/**
 * This class allows us to gath all statistics of a solver.
 * 
 * @author Christophe Lecoutre
 */
public final class Statistics implements ObserverSearch, ObserverRuns, ObserverDecisions {

	private static NumberFormat nformat = NumberFormat.getInstance();

	/*************************************************************************
	 ***** Implemented Interfaces
	 *************************************************************************/

	@Override
	public final void beforePreprocessing() {
		stopwatch.start();
		nPreproAddedNogoods = solver.nogoodRecorder != null ? solver.nogoodRecorder.nNogoods : 0;
		nPreproAddedCtrs = solver.problem.constraints.length;
	}

	@Override
	public final void afterPreprocessing() {
		preproWck += stopwatch.wckTime();
		nPreproAddedNogoods = solver.nogoodRecorder != null ? solver.nogoodRecorder.nNogoods - nPreproAddedNogoods : 0;
		nPreproAddedCtrs = solver.problem.constraints.length - nPreproAddedCtrs;
		nPreproRemovedValues = Variable.nRemovedValuesFor(solver.problem.variables);
		nPreproRemovedTuples = solver.propagation.nTuplesRemoved;
	}

	@Override
	public final void beforeSolving() {
		stopwatch.start();
	}

	@Override
	public final void afterSolving() {
		solvingWck += stopwatch.wckTime();
	}

	@Override
	public void afterRun() {
		searchWck = stopwatch.wckTime();
	}

	@Override
	public void beforePositiveDecision(Variable x, int a) {
		nNodes++;
		if (x.dom.size() > 1)
			nDecisions++;
		// nAssignments++; done elsewhere
	}

	@Override
	public void beforeNegativeDecision(Variable x, int a) {
		if (x.dom.size() > 1) {
			nNodes++;
			nDecisions++;
		}
	}

	/*************************************************************************
	 ***** Fields and Methods
	 *************************************************************************/

	/**
	 * The solver to which the object is attached
	 */
	public final Solver solver;

	public final Stopwatch stopwatch = new Stopwatch();

	public long nNodes = 1, nDecisions, nWrongDecisions, nBacktracks, nAssignments, nFailedAssignments;

	public long nPreproRemovedValues, nPreproRemovedTuples, nPreproAddedCtrs, nPreproAddedNogoods;

	public long solvingWck, preproWck, searchWck, firstSolWck, firstSolCpu, lastSolWck, lastSolCpu;

	private long tmpNbAssignments, tmpNbBacktracks, tmpNbFailedAssignments;

	public Statistics(Solver solver) {
		this.solver = solver;
	}

	public long numberSafe() {
		return nNodes + nAssignments + nBacktracks;
	}

	public void store() {
		tmpNbAssignments = nAssignments;
		tmpNbFailedAssignments = nFailedAssignments;
		tmpNbBacktracks = nBacktracks;
	}

	public void restore() {
		nAssignments = tmpNbAssignments;
		nFailedAssignments = tmpNbFailedAssignments;
		nBacktracks = tmpNbBacktracks;
	}

	public final long nRevisions() {
		return solver.propagation instanceof Forward ? ((Forward) solver.propagation).reviser.nRevisions : 0;
	}

	public final long nUselessRevisions() {
		return solver.propagation instanceof Forward ? ((Forward) solver.propagation).reviser.nUselessRevisions : 0;
	}

	public void manageSolution() {
		long cpu = solver.head.stopwatch.cpuTime(), wck = solver.head.instanceStopwatch.wckTime();
		if (solver.solutions.found == 1) {
			firstSolCpu = cpu;
			firstSolWck = wck;
		}
		lastSolCpu = cpu;
		lastSolWck = wck;
	}

	public final Attributes solverAttributes() {
		Attributes m = new Attributes(SOLVER);
		m.put(GUARANTEED_GAC, solver.propagation.getClass() == GAC.class ? ((GAC) solver.propagation).guaranteed : "");
		m.separator();
		m.put(WCK, solver.head.instanceStopwatch.wckTimeInSeconds());
		m.put(CPU, solver.head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	public final Attributes preproAttributes() {
		Attributes m = new Attributes(PREPROCESSING);
		m.put(N_EFFECTIVE, solver.problem.features.nEffectiveFilterings);
		m.put(REVISIONS, "(" + nRevisions() + ",useless=" + nUselessRevisions() + ")", nRevisions() > 0);
		m.put(N_VALUES, Variable.nValidValuesFor(solver.problem.variables));
		m.put(REMOVED_BY_AC, solver.propagation instanceof GAC ? ((GAC) (solver.propagation)).nPreproValueRemovals : 0);
		// m.put("nTotalRemovedValues", nPreproRemovedValues);
		m.put(UNSAT, solver.stopping == EStopping.FULL_EXPLORATION);
		m.separator(nPreproRemovedTuples > 0 || nPreproAddedNogoods > 0 || nPreproAddedCtrs > 0);
		m.put(N_REMOVED_TUPLES, nPreproRemovedTuples);
		m.put(N_NOGOODS, nPreproAddedNogoods);
		m.put(N_ADDED_CTRS, nPreproAddedCtrs);
		m.separator(solver.propagation.nSingletonTests > 0);
		m.put(N_SINGLETON_TESTS, solver.propagation.nSingletonTests);
		m.put(N_EFFECTIVE_SINGLETON_TESTS, solver.propagation.nEffectiveSingletonTests);
		m.put(N_FOUND_SINGLETONS, solver.propagation instanceof SAC ? ((SAC) (solver.propagation)).nFoundSingletons : 0);
		m.put(N_BUILT_BRANCHES, solver.propagation instanceof SACGreedy ? ((SACGreedy) (solver.propagation)).nBranchesBuilt : 0);
		m.put(SUM_BRANCH_SIZES, solver.propagation instanceof SACGreedy ? ((SACGreedy) (solver.propagation)).sumBranchSizes : 0);
		m.separator();
		m.put(SOLS, solver.solutions.found);
		m.put(SOL1_CPU, firstSolCpu / 1000.0, solver.solutions.found > 0);
		m.put(WCK, preproWck / 1000.0);
		m.put(CPU, solver.head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	public Attributes runAttributes() {
		Attributes m = new Attributes(RUN);
		m.put("run", solver.restarter.numRun);
		m.put(DEPTHS, solver.minDepth + ".." + solver.maxDepth);
		m.put(N_EFFECTIVE, solver.problem.features.nEffectiveFilterings);
		m.put(N_WRONG, nWrongDecisions);
		if (Kit.memory() > 10000000000L)
			m.put(MEM, Kit.memoryInMb());
		m.put(WCK, stopwatch.wckTimeInSeconds());
		m.put(N_NOGOODS, solver.nogoodRecorder != null ? solver.nogoodRecorder.nNogoods : 0);
		if (solver.solutions.found > 0) {
			if (solver.problem.settings.framework == TypeFramework.CSP)
				m.put(SOLS, solver.solutions.found);
			else {
				if (solver.problem.optimizer.minBound == 0 || solver.problem.optimizer.minBound == Long.MIN_VALUE)
					m.put(BOUND, nformat.format(solver.solutions.bestBound));
				else
					m.put(BOUNDS, solver.problem.optimizer.stringBounds());
			}
		}
		if (solver.head.control.general.verbose <= 1)
			return m;
		m.separator();
		m.put(N_DECISIONS, nDecisions);
		m.put(N_BACKTRACKS, nBacktracks);
		m.put(N_FAILED, nFailedAssignments);
		m.put(REVISIONS, "(" + nRevisions() + ",useless=" + nUselessRevisions() + ")", nRevisions() > 0);
		m.put(N_SINGLETON_TESTS, solver.propagation.nSingletonTests);
		m.put(N_EFFECTIVE_SINGLETON_TESTS, solver.propagation.nEffectiveSingletonTests);
		if (Kit.memory() > 10000000000L)
			m.put(MEM, Kit.memoryInMb());
		m.separator();
		if (solver.ipsRecorder instanceof IpsRecorderForEquivalence && !solver.ipsRecorder.stopped) {
			IpsRecorderForEquivalence recorder = (IpsRecorderForEquivalence) solver.ipsRecorder;
			m.put(MAP_SIZE, recorder.getMapSize());
			m.put(N_INFERENCES, recorder.nInferences);
			m.put(N_TOO_LARGE_KEYS, recorder.nTooLargeKeys);
		}
		if (solver.ipsRecorder != null) {
			ReductionOperator ro = solver.ipsRecorder.reductionOperator;
			m.put(N_SELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbSEliminableVariables()));
			m.put(N_RELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbREliminableVariables()));
			m.put(N_IELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbIEliminableVariables()));
			m.put(N_DELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbDEliminableVariables()));
			m.put(N_PELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbPEliminableVariables()));
			m.separator();
		}
		return m;
	}

	public Attributes globalAttributes() {
		Attributes m = new Attributes(GLOBAL);
		m.put(N_EFFECTIVE, solver.problem.features.nEffectiveFilterings);
		m.put(REVISIONS, "(" + nRevisions() + ",useless=" + nUselessRevisions() + ")", nRevisions() > 0);
		m.put(N_SINGLETON_TESTS, solver.propagation.nSingletonTests);
		m.put(N_EFFECTIVE_SINGLETON_TESTS, solver.propagation.nEffectiveSingletonTests);
		m.put(N_NOGOODS, solver.nogoodRecorder != null ? solver.nogoodRecorder.nNogoods : 0);
		m.separator();
		m.put(STOP, solver.stopping == null ? "no" : solver.stopping.toString());
		m.put(N_WRONG, solver.stats.nWrongDecisions);
		if (solver.solutions.found > 0) {
			if (solver.problem.settings.framework != TypeFramework.CSP) {
				m.put(BOUND, solver.solutions.bestBound);
				m.put(BOUND_WCK, lastSolWck / 1000.0);
				m.put(BOUND_CPU, lastSolCpu / 1000.0);
			}
			m.put(SOLS, solver.solutions.found);
			m.put(SOL1_CPU, firstSolCpu / 1000.0);
		}
		m.separator();
		m.put(WCK, solver.head.instanceStopwatch.wckTimeInSeconds());
		m.put(CPU, solver.head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

}