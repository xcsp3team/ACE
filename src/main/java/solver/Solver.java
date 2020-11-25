/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package solver;

import static utility.Enums.EStopping.EXCEEDED_TIME;
import static utility.Enums.EStopping.FULL_EXPLORATION;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import interfaces.Observers.ObserverAssignment;
import interfaces.Observers.ObserverConflicts;
import interfaces.Observers.ObserverRuns;
import interfaces.Observers.ObserverSearch;
import interfaces.Tags.TagBinaryRelationFiltering;
import main.Head;
import problem.Problem;
import propagation.Propagation;
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
	public final Head head;

	/**
	 * The problem to be solved
	 */
	public final Problem problem;

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
	public EStopping stopping;

	public Statistics stats;

	public final boolean isFullExploration() {
		return stopping == FULL_EXPLORATION;
	}

	public final boolean finished() {
		if (stopping != null)
			return true;
		if (head.isTimeExpiredForCurrentInstance()) {
			stopping = EXCEEDED_TIME;
			return true;
		}
		return false;
	}

	public final void resetNoSolutions() {
		stopping = null;
		solManager.found = 0;
	}

	public void reset() { // called by very special objects (for example, when extracting a MUC)
		Kit.control(futVars.nDiscarded() == 0);
		Kit.control(!(propagation instanceof TagBinaryRelationFiltering), () -> "for the moment");
		propagation.reset();
		restarter.reset();
		resetNoSolutions();
	}

	/**********************************************************************************************
	 * Constructor + methods
	 *********************************************************************************************/

	public Solver(Head head) {
		this.head = head;
		this.problem = head.problem;
		this.problem.solver = this;
		this.futVars = new FutureVariables(problem.variables);
		this.solManager = new SolutionManager(this, head.control.general.nSearchedSolutions); // build solutionManager before propagation
		this.propagation = Propagation.buildFor(this); // may be null
		if (!head.control.propagation.useAuxiliaryQueues)
			Stream.of(problem.constraints).forEach(c -> c.filteringComplexity = 0);
		this.restarter = Restarter.buildFor(this);
		this.observersSearch = Stream.of(problem.constraints).filter(c -> c instanceof ObserverSearch).map(c -> (ObserverSearch) c)
				.collect(Collectors.toCollection(ArrayList::new));
		observersSearch.add(head.output);
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
			stopping = FULL_EXPLORATION;
		for (ObserverSearch observer : observersSearch)
			observer.afterPreprocessing();
	}

	/**
	 * Starts a run of the search.
	 */
	public abstract Solver doRun();

	// public Variable impacting;

	int diviser = 1;

	protected final void doSearch() {
		for (ObserverSearch observer : observersSearch)
			observer.beforeSearch();
		while (!finished() && !restarter.allRunsFinished()) {
			for (ObserverRuns observer : observersRuns)
				observer.beforeRun();

			// boolean b = restarter.numRun % diviser == 0;
			// if (restarter.numRun % 20 == 0)
			// diviser++;
			// System.out.println("bbbb " + b);
			// if (b) {
			// Domain.setMarks(pb.variables);
			// if (solManager.found > 0) {
			// SumSimpleLE c = (SumSimpleLE) pb.optimizer.ctr;
			// Variable x = c.mostImpacting();
			// int v = x.dom.toVal(solManager.lastSolution[x.num]);
			// x.dom.removeValuesGE(v);
			// System.out.println("ccccc most " + x + " " + x.dom.toVal(solManager.lastSolution[x.num]));
			// }
			// }

			if (stopping != FULL_EXPLORATION) // an observer might modify the object stoppingType
				doRun();

			// if (b)
			// Domain.restoreAtMarks(pb.variables);

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
		if (Variable.firstWipeoutVariableIn(problem.variables) != null)
			stopping = FULL_EXPLORATION;
		if (!finished() && head.control.solving.enablePrepro)
			doPrepro();
		if (!finished() && head.control.solving.enableSearch)
			doSearch();
		for (ObserverSearch observer : observersSearch)
			observer.afterSolving();
	}
}