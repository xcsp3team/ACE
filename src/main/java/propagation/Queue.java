/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package propagation;

import java.util.stream.Collectors;
import java.util.stream.IntStream;

import heuristics.HeuristicRevisions;
import heuristics.HeuristicRevisions.HeuristicRevisionsDirect.First;
import main.Head;
import sets.SetSparse;
import utility.Reflector;
import variables.Variable;

/**
 * A queue is used to store the variables that have to be considered by constraint propagation. A variable is added to the queue when its domain has been
 * reduced so as to propagate this event. Constraint propagation iteratively involves picking one variable in this set (by means of a so-called revision
 * ordering heuristic) and then performs some filtering.
 * 
 * @author Christophe Lecoutre
 */
public final class Queue extends SetSparse {

	/**
	 * The propagation to which the queue is attached
	 */
	public final Forward propagation;

	public final SmallestDomainVariable enqueuedSmallestDomainVariable;

	/**
	 * The revision ordering heuristic used to pick variables from the queue.
	 */
	private final HeuristicRevisions heuristic;

	/**
	 * The variables of the problem; redundant field
	 */
	private final Variable[] variables;

	/**
	 * The number of times a variable has been picked from the queue
	 */
	public int nPicks;

	/**
	 * Builds a queue for storing variables whose domains have been reduced (and so, must be propagated)
	 * 
	 * @param propagation
	 *            the propagation object to which the queue is attached
	 */
	public Queue(Forward propagation) {
		super(propagation.solver.head.problem.variables.length);
		this.propagation = propagation;
		this.enqueuedSmallestDomainVariable = new SmallestDomainVariable(); // keep at this position
		Head head = propagation.solver.head;
		String className = head.problem.features.maxDomSize() <= 4 ? First.class.getSimpleName() : head.control.revh.clazz;
		// above, 4 is used arbitrarily (hard coding)
		this.heuristic = Reflector.buildObject(className, head.availableClasses.get(HeuristicRevisions.class), this, head.control.revh.anti);
		this.variables = head.problem.variables;

	}

	public class SmallestDomainVariable {

		public int domSizeLowerBound;

		private Variable variable;

		private int position;

		void clear() {
			domSizeLowerBound = Integer.MAX_VALUE;
			variable = null;
			position = 0;
		}

		void consider(Variable x) {
			if (x.dom.size() < domSizeLowerBound) {
				domSizeLowerBound = x.dom.size();
				variable = x;
				position = sparse[x.num];
			}
		}

		public int validVariable() {
			if (variable != null && position <= limit && var(position) == variable)
				return position;
			return -1;
		}
	}

	@Override
	public void clear() {
		super.clear();
		enqueuedSmallestDomainVariable.clear();
	}

	/**
	 * Returns the ith variable from the queue
	 * 
	 * @param i
	 *            the index of the variable in the queue to be returned
	 * @return the variable at index i in the queue
	 */
	public Variable var(int i) {
		assert 0 <= i && i <= limit;
		return variables[dense[i]];
	}

	/**
	 * Adds the specified variable to the queue. This method must be called when the domain of the specified variable has been modified.
	 * 
	 * @param x
	 *            a variable to be added
	 */
	public void add(Variable x) {
		x.time = propagation.incrementTime();
		add(x.num);
		enqueuedSmallestDomainVariable.consider(x);
		assert !x.assigned() || x == propagation.solver.futVars.lastPast() : "variable " + x;
	}

	/**
	 * Add all variables of the problem (constraint network) to the queue
	 */
	@Override
	public void fill() {
		for (Variable x : variables)
			if (!x.assigned() || x == propagation.solver.futVars.lastPast())
				add(x);
	}

	/**
	 * Picks and deletes the ith variable in the queue
	 * 
	 * @param i
	 *            the index of the variable in the queue to be returned (and deleted from the queue)
	 * @return the ith variable in the queue
	 */
	public Variable pickAndDelete(int i) {
		nPicks++;
		int num = dense[i];
		remove(num);
		return variables[num];
	}

	/**
	 * Picks and deletes a variable in the queue, which is chosen by the revision ordering heuristic.
	 * 
	 * @return a variable of the queue
	 */
	public Variable pickAndDelete() {
		if (propagation.solver.profiler != null)
			propagation.solver.profiler.before();
		Variable x = pickAndDelete(heuristic.bestInQueue());
		if (propagation.solver.profiler != null)
			propagation.solver.profiler.afterSelectingInQueue();
		return x;
	}

	public void incrementTimeOfPresentVariables() {
		for (int i = limit; i >= 0; i--)
			variables[dense[i]].time = propagation.incrementTime();
	}

	@Override
	public String toString() {
		return "There are " + size() + " elements : " + IntStream.range(0, size()).mapToObj(i -> var(i) + " ").collect(Collectors.joining());
	}

}