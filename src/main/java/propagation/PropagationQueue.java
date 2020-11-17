/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation;

import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import heuristics.HeuristicRevisions;
import heuristics.HeuristicRevisions.HeuristicRevisionsDirect.First;
import learning.LearnerNogoods;
import learning.LearnerStatesDominance;
import propagation.order1.PropagationForward;
import sets.SetSparse;
import utility.Reflector;
import variables.Domain;
import variables.Variable;

/**
 * This class is used to store the elements that have to be taken into account by constraint propagation. Constraint propagation iteratively involves picking
 * one element in this set (by means of a so-called revision ordering heuristic) and then performs some filtering.
 */
public final class PropagationQueue extends SetSparse {

	public final PropagationForward propagation;

	private final HeuristicRevisions heuristic;

	private final Variable[] variables; // variables of the problem ; redundant field

	public int nPicks;

	public PropagationQueue(PropagationForward propagation) {
		super(propagation.pb().variables.length);
		this.propagation = propagation;
		String className = propagation.pb().stuff.maxDomSize() <= 4 ? First.class.getSimpleName() : propagation.cp().settingRevh.classForRevHeuristic;
		Set<Class<?>> classes = propagation.solver.rs.handlerClasses.map.get(HeuristicRevisions.class);
		this.heuristic = Reflector.buildObject(className, classes, this, propagation.cp().settingRevh.anti);
		this.variables = propagation.pb().variables;
	}

	/**
	 * Returns the ith variable in the queue.
	 */
	public Variable var(int i) {
		assert 0 <= i && i <= limit;
		return variables[dense[i]];
	}

	/**
	 * Add the specified variable to the queue. It must be called when the domain of the specified variable has been modified.
	 */
	public void add(Variable x) {
		x.timestamp = propagation.incrementTime();
		add(x.num);
		assert !x.isAssigned() || x == propagation.solver.futVars.lastPast() : "variable " + x;
	}

	/**
	 * Add all variables to the queue.
	 */
	@Override
	public PropagationQueue fill() {
		for (Variable x : variables)
			if (!x.isAssigned() || x == propagation.solver.futVars.lastPast())
				add(x);
		return this;
	}

	/**
	 * Pick and delete the ith variable in the queue.
	 */
	public Variable pickAndDelete(int i) {
		nPicks++;
		int num = dense[i];
		remove(num);
		return variables[num];
	}

	/**
	 * Pick and delete a variable in the queue, chosen by the underlying revision ordering heuristic.
	 */
	public Variable pickAndDelete() {
		return pickAndDelete(heuristic.bestPosition());
	}

	public boolean isNogoodConsistent(Variable x) {
		if (learnerNogood != null) {
			// if (propagation.getSolver().getResolution().getAuxiliarySolver() == propagation.getSolver()) return true;
			// for the moment the auxiliary solver does not exploit nogoods
			if (x.dom.size() == 1 && learnerNogood.checkWatchesOf(x, x.dom.first(), false) == false)
				return false;
		}
		if (sentinelLevel != null) {
			if (sentinelLevel[x.num] != propagation.solver.stats.numberSafe())
				absentValuesSentinel[x.num] = -1;
			int depth = propagation.solver.depth();
			Domain dom = x.dom;
			int last = dom.lastRemoved();
			for (int a = dom.lastRemoved(); a != absentValuesSentinel[x.num] && dom.isRemovedAtLevel(a, depth); a = dom.prevRemoved(a)) {
				// if (elements.getAbsentLevelOf(index) < depth) // TODO ex version, the new one (with isAtLevel) must be controlled
				// break;
				if (!stateDominanceManager.checkWatchesOf(x.num, a))
					return false;
			}
			sentinelLevel[x.num] = propagation.solver.stats.numberSafe();
			absentValuesSentinel[x.num] = last;
		}
		return true;
	}

	public void incrementTimestampsOfEnqueuedVariables() {
		for (int i = limit; i >= 0; i--)
			variables[dense[i]].timestamp = propagation.incrementTime();
	}

	@Override
	public String toString() {
		return "There are " + size() + " elements : " + IntStream.range(0, size()).mapToObj(i -> var(i) + " ").collect(Collectors.joining());
	}

	/**********************************************************************************************
	 * Fields below, together with setter methods, are for learning ; not necessarily used
	 *********************************************************************************************/

	private LearnerNogoods learnerNogood;

	private LearnerStatesDominance stateDominanceManager;

	private int[] absentValuesSentinel;

	private long[] sentinelLevel;

	public void setLearnerNogood(LearnerNogoods nogoodManager) {
		this.learnerNogood = nogoodManager;
	}

	public void setStateDominanceManager(LearnerStatesDominance stateDominanceManager) {
		this.stateDominanceManager = stateDominanceManager;
		this.absentValuesSentinel = new int[propagation.solver.pb.variables.length];
		this.sentinelLevel = new long[absentValuesSentinel.length];
	}

}