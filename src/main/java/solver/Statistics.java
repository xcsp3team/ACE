/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package solver;

import static dashboard.Output.CPU;
import static dashboard.Output.MEM;
import static dashboard.Output.WCK;

import java.text.NumberFormat;

import org.xcsp.common.Types.TypeFramework;

import interfaces.Observers.ObserverDecisions;
import interfaces.Observers.ObserverRuns;
import interfaces.Observers.ObserverSearch;
import learning.IpsRecorderForEquivalence;
import learning.ReductionOperator;
import problem.Features.MapAtt;
import propagation.Forward;
import propagation.GAC;
import propagation.SAC;
import propagation.SAC.SACGreedy;
import utility.Enums.EStopping;
import utility.Kit;
import utility.Kit.Stopwatch;
import variables.Variable;

/**
 * This class allows gathering all statistics of a given solver.
 */
public abstract class Statistics implements ObserverSearch, ObserverRuns, ObserverDecisions {

	public static final String N_BUILT_BRANCHES = "nBuiltBranches";
	public static final String SUM_BRANCH_SIZES = "sumBranchSizes";
	public static final String MAP_SIZE = "mapSize";
	public static final String N_INFERENCES = "nInferences";
	public static final String N_TOO_LARGE_KEYS = "nTooLargeKeys";
	public static final String N_SELIMINABLES = "nSEliminables";
	public static final String N_RELIMINABLES = "nREliminables";
	public static final String N_DELIMINABLES = "nDEliminables";
	public static final String N_IELIMINABLES = "nIEliminables";
	public static final String N_PELIMINABLES = "nPEliminables";
	public static final String N_SINGLETON_TESTS = "nSingletonTests";
	public static final String N_EFFECTIVE_SINGLETON_TESTS = "nEffectiveSingletonTests";
	public static final String N_FOUND_SINGLETONS = "nFoundSingletons";
	public static final String GUARANTEED_GAC = "guaranteedGAC";
	public static final String STOP = "Stop";

	private static NumberFormat nformat = NumberFormat.getInstance();

	/*************************************************************************
	 ***** Implemented Interfaces
	 *************************************************************************/

	@Override
	public final void beforePreprocessing() {
		stopwatch.start();
		if (solver instanceof Solver && solver.nogoodRecorder != null)
			nPreproAddedNogoods = solver.nogoodRecorder.nNogoods;
		nPreproAddedCtrs = solver.problem.constraints.length;
	}

	@Override
	public final void afterPreprocessing() {
		preproWck += stopwatch.wckTime();
		if (solver instanceof Solver && solver.nogoodRecorder != null)
			nPreproAddedNogoods = solver.nogoodRecorder.nNogoods - nPreproAddedNogoods;
		nPreproAddedCtrs = solver.problem.constraints.length - nPreproAddedCtrs;
		nPreproRemovedValues = Variable.nRemovedValuesFor(solver.problem.variables);
		nPreproRemovedTuples = solver.propagation.nTuplesRemoved;
		nPreproInconsistencies = solver.stopping == EStopping.FULL_EXPLORATION ? 1 : 0;
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

	public final Solver solver;

	public final Stopwatch stopwatch = new Stopwatch();

	public long nNodes = 1, nDecisions, nWrongDecisions, nBacktracks, nAssignments, nFailedAssignments;

	public long nPreproRemovedValues, nPreproRemovedTuples, nPreproAddedCtrs, nPreproAddedNogoods, nPreproInconsistencies;

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

	public final long nEffectiveFilterings() {
		return solver.problem.features.nEffectiveFilterings;
	}

	public final long nRevisions() {
		return solver.propagation instanceof Forward ? ((Forward) solver.propagation).reviser.nRevisions : 0;
	}

	public final long nUselessRevisions() {
		return solver.propagation instanceof Forward ? ((Forward) solver.propagation).reviser.nUselessRevisions : 0;
	}

	public final long nSingletonTests() {
		return solver.propagation.nSingletonTests;
	}

	public final long nEffectiveSingletonTests() {
		return solver.propagation.nEffectiveSingletonTests;
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

	public final MapAtt solverAttributes() {
		MapAtt m = new MapAtt("Solver");
		if (solver.propagation.getClass() == GAC.class)
			m.put(GUARANTEED_GAC, ((GAC) solver.propagation).guaranteed);
		m.separator();
		m.put(WCK, solver.head.instanceStopwatch.wckTimeInSeconds());
		m.put(CPU, solver.head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	public final MapAtt preproAttributes() {
		MapAtt m = new MapAtt("Preprocessing");
		m.put("eff", nEffectiveFilterings());
		m.putIf("revisions", "(" + nRevisions() + ",useless=" + nUselessRevisions() + ")", nRevisions() > 0);
		m.put("nValues", Variable.nValidValuesFor(solver.problem.variables));
		if (solver.propagation instanceof GAC)
			m.put("nACremovedValues", ((GAC) (solver.propagation)).nPreproValueRemovals);
		// m.put("nTotalRemovedValues", nPreproRemovedValues);
		m.put("inconsistency", nPreproInconsistencies > 0);
		m.separator();
		if (nPreproRemovedTuples > 0 || nPreproAddedNogoods > 0 || nPreproAddedCtrs > 0) {
			m.put("nRemovedTuples", nPreproRemovedTuples);
			m.put("nNogoods", nPreproAddedNogoods);
			m.put("nAddedCtrs", nPreproAddedCtrs);
			m.separator();
		}
		if (nSingletonTests() > 0) {
			m.put(N_SINGLETON_TESTS, nSingletonTests());
			m.put(N_EFFECTIVE_SINGLETON_TESTS, nEffectiveSingletonTests());
			if (solver.propagation instanceof SAC)
				m.put(N_FOUND_SINGLETONS, ((SAC) (solver.propagation)).nFoundSingletons);
			if (solver.propagation instanceof SACGreedy) {
				m.put(N_BUILT_BRANCHES, ((SACGreedy) (solver.propagation)).nBranchesBuilt);
				m.put(SUM_BRANCH_SIZES, ((SACGreedy) (solver.propagation)).sumBranchSizes);
			}
			m.separator();
		}
		if (solver.solutions.found > 0) {
			m.put("foundSolutions", solver.solutions.found);
			m.put("firstSolCpu", firstSolCpu / 1000.0);
			m.separator();
		}
		m.put(WCK, preproWck / 1000.0);
		m.put(CPU, solver.head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	public abstract MapAtt runAttributes();

	public abstract MapAtt cumulatedAttributes();

	// private boolean statMouny = true;

	public MapAtt globalAttributes() {
		MapAtt m = cumulatedAttributes();
		// m.put(EXPIRED_TIME, solver.rs.isTimeExpiredForCurrentInstance());
		// m.put(TOTAL_EXPLORATION, solver.isFullExploration());
		m.put(STOP, solver.stopping == null ? "no" : solver.stopping.toString());
		m.put("wrong", solver.stats.nWrongDecisions);
		// if (statMouny && solver.propagation instanceof ACPartial) {
		// int[] t = ((ACPartial) solver.propagation).statistics;
		// map.put("nbWOs", t[0] + ""); map.put("nbFPs", t[1] + ""); map.put("avgWOs", t[2] + ""); map.put("avgFPs", t[3] + ""); }
		if (solver.solutions.found > 0) {
			if (solver.problem.settings.framework != TypeFramework.CSP) {
				m.put("bestBound", solver.solutions.bestBound);
				m.put("bestBoundWck", lastSolWck / 1000.0);
				m.put("bestBoundCpu", lastSolCpu / 1000.0);
			}
			m.put("foundSolutions", solver.solutions.found);
			m.put("firstSolCpu", firstSolCpu / 1000.0);
			m.separator();
		}
		m.put(WCK, solver.head.instanceStopwatch.wckTimeInSeconds());
		m.put(CPU, solver.head.stopwatch.cpuTimeInSeconds());
		m.put(MEM, Kit.memoryInMb());
		return m;
	}

	/*************************************************************************
	 ***** StatisticsBacktrack
	 *************************************************************************/

	public static final class StatisticsBacktrack extends Statistics {

		protected Solver solver;

		public StatisticsBacktrack(Solver solver) {
			super(solver);
			this.solver = solver;
		}

		@Override
		public MapAtt runAttributes() {
			MapAtt m = new MapAtt("Run");
			m.put("run", solver.restarter.numRun);
			m.put("dpt", solver.minDepth + ".." + solver.maxDepth);
			m.put("eff", nEffectiveFilterings());
			m.put("wrg", nWrongDecisions);
			if (Kit.memory() > 10000000000L)
				m.put(MEM, Kit.memoryInMb());
			m.put(WCK, stopwatch.wckTimeInSeconds());
			if (solver.nogoodRecorder != null)
				m.putWhenPositive("ngd", solver.nogoodRecorder.nNogoods);
			if (solver.solutions.found > 0) {
				if (solver.problem.settings.framework == TypeFramework.CSP)
					m.put("nSols", solver.solutions.found);
				else {
					if (solver.problem.optimizer.minBound == 0 || solver.problem.optimizer.minBound == Long.MIN_VALUE)
						m.put("bnd", nformat.format(solver.solutions.bestBound));
					else
						m.put("bnds", solver.problem.optimizer.stringBounds());
					// m.put("bnd", nformat.format(solver.solManager.bestBound));
				}
			}
			if (solver.head.control.general.verbose <= 1)
				return m;
			m.separator();
			m.put("decs", nDecisions);
			m.put("backs", nBacktracks);
			m.put("failed", nFailedAssignments);
			m.putIf("revisions", "(" + nRevisions() + ",useless=" + nUselessRevisions() + ")", nRevisions() > 0);
			if (nSingletonTests() > 0) { // solver.getPreproPropagationTechnique() instanceof SingletonArcConsistency) {
				m.put(N_SINGLETON_TESTS, nSingletonTests());
				m.put(N_EFFECTIVE_SINGLETON_TESTS, nEffectiveSingletonTests());
			}
			if (Kit.memory() > 10000000000L)
				m.put(MEM, Kit.memoryInMb());
			m.separator();
			if (solver.ipsRecorder != null && solver.ipsRecorder instanceof IpsRecorderForEquivalence && !solver.ipsRecorder.stopped) {
				IpsRecorderForEquivalence learner = (IpsRecorderForEquivalence) solver.ipsRecorder;
				m.put(MAP_SIZE, learner.getMapSize());
				m.put(N_INFERENCES, learner.nInferences);
				// map.put("nbInferredSolutions", solutionCounter.nbInferredSolutions );
				m.put(N_TOO_LARGE_KEYS, learner.nTooLargeKeys);
			}
			if (solver.ipsRecorder != null) {
				ReductionOperator ro = solver.ipsRecorder.reductionOperator;
				// DecimalFormat df = new DecimalFormat("###.##",new DecimalFormatSymbols(Locale.ENGLISH));
				m.put(N_SELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbSEliminableVariables()));
				m.put(N_RELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbREliminableVariables()));
				m.put(N_IELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbIEliminableVariables()));
				m.put(N_DELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbDEliminableVariables()));
				m.put(N_PELIMINABLES, Kit.decimalFormat.format(ro.getProportionOfNbPEliminableVariables()));
				m.separator();
			}
			return m;
		}

		@Override
		public MapAtt cumulatedAttributes() {
			MapAtt m = new MapAtt("Global");
			m.put("eff", nEffectiveFilterings());
			m.putIf("revisions", "(" + nRevisions() + ",useless=" + nUselessRevisions() + ")", nRevisions() > 0);
			if (nSingletonTests() > 0) { // solver.getPreproPropagationTechnique() instanceof SingletonArcConsistency) {
				m.put(N_SINGLETON_TESTS, nSingletonTests());
				m.put(N_EFFECTIVE_SINGLETON_TESTS, nEffectiveSingletonTests());
			}

			if (solver.nogoodRecorder != null)
				m.putWhenPositive("nogoods", solver.nogoodRecorder.nNogoods);
			m.separator();
			return m;
		}
	}

}