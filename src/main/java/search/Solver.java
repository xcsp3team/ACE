/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search;

import static utility.Enums.EStopping.EXCEEDED_TIME;
import static utility.Enums.EStopping.FULL_EXPLORATION;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import executables.Resolution;
import interfaces.ObserverAssignment;
import interfaces.ObserverConflicts;
import interfaces.ObserverRuns;
import interfaces.ObserverSearch;
import interfaces.TagBinaryRelationFiltering;
import problem.Problem;
import propagation.Propagation;
import search.statistics.Statistics;
import utility.Enums.EStopping;
import utility.Kit;
import variables.Variable;

public abstract class Solver {

	/**********************************************************************************************
	 * Observers
	 *********************************************************************************************/

	public final List<ObserverSearch> observersSearch;

	public List<ObserverRuns> observersRuns;

	public List<ObserverAssignment> observersAssignment;

	public List<ObserverConflicts> observersConflicts;

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	/**
	 * The main object
	 */
	public final Resolution rs;

	/**
	 * The problem to be solved
	 */
	public final Problem pb;

	public final FutureVariables futVars;

	public final SolutionManager solManager;

	/**
	 * The object that implements the restarts policy of the solver.
	 */
	public final Restarter restarter;

	public Propagation propagation;

	/**
	 * when null, the solver is still running
	 */
	public EStopping stoppingType;

	public Statistics stats;

	public final boolean isFullExploration() {
		return stoppingType == FULL_EXPLORATION;
	}

	public final boolean finished() {
		if (stoppingType != null)
			return true;
		if (rs.isTimeExpiredForCurrentInstance()) {
			stoppingType = EXCEEDED_TIME;
			return true;
		}
		return false;
	}

	public final void resetNoSolutions() {
		stoppingType = null;
		solManager.found = 0;
	}

	public void reset(boolean preserveWeightedDegrees) {
		Kit.control(futVars.nDiscarded() == 0);
		Kit.control(!(propagation instanceof TagBinaryRelationFiltering), () -> "for the moment");
		propagation.reset();
		restarter.reset();
		resetNoSolutions();
	}

	/**********************************************************************************************
	 * Constructor + methods
	 *********************************************************************************************/

	public Solver(Resolution resolution) {
		this.rs = resolution;
		this.pb = resolution.problem;
		this.pb.solver = this;
		this.futVars = new FutureVariables(pb.variables);
		this.solManager = new SolutionManager(this, resolution.cp.settingGeneral.nSearchedSolutions); // build solutionManager before propagation
		this.propagation = Propagation.buildFor(this); // may be null
		if (!resolution.cp.settingPropagation.useAuxiliaryQueues)
			Stream.of(pb.constraints).forEach(c -> c.filteringComplexity = 0);
		this.restarter = Restarter.buildFor(this);
		this.observersSearch = Stream.of(pb.constraints).filter(c -> c instanceof ObserverSearch).map(c -> (ObserverSearch) c)
				.collect(Collectors.toCollection(ArrayList::new));
		observersSearch.add(resolution.output);
	}

	/**
	 * Returns the current depth (of the current search) of the solver.
	 */
	public abstract int depth();

	public abstract void pushVariable(Variable x);

	public abstract void assign(Variable x, int a);

	public abstract void backtrack(Variable x);

	public abstract void backtrack();

	private final void doPrepro() {
		for (ObserverSearch observer : observersSearch)
			observer.beforePreprocessing();
		if (propagation.runInitially() == false)
			stoppingType = FULL_EXPLORATION;
		for (ObserverSearch observer : observersSearch)
			observer.afterPreprocessing();
	}

	/**
	 * Starts a run of the search.
	 */
	public abstract Solver doRun();

	protected final void doSearch() {
		for (ObserverSearch observer : observersSearch)
			observer.beforeSearch();
		while (!finished() && !restarter.allRunsFinished()) {
			for (ObserverRuns observer : observersRuns)
				observer.beforeRun();
			if (stoppingType != FULL_EXPLORATION) // an observer might modify the object stoppingType
				doRun();
			for (ObserverRuns observer : observersRuns)
				observer.afterRun();
		}
		for (ObserverSearch observer : observersSearch)
			observer.afterSearch();
	}

	/**
	 * This method allows to solve the attached problem instance.
	 */
	public void solve() {
		for (ObserverSearch observer : observersSearch)
			observer.beforeSolving();
		if (Variable.firstWipeoutVariableIn(pb.variables) != null)
			stoppingType = FULL_EXPLORATION;
		if (!finished() && rs.cp.settingSolving.enablePrepro)
			doPrepro();
		if (!finished() && rs.cp.settingSolving.enableSearch)
			doSearch();
		for (ObserverSearch observer : observersSearch)
			observer.afterSolving();
	}
}