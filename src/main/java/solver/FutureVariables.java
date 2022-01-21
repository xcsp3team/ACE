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

import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.function.Consumer;
import java.util.stream.IntStream;

import variables.Variable;

/**
 * This class allows us to manage past and future variables. It is used by solvers.
 * 
 * @author Christophe Lecoutre
 */
public final class FutureVariables implements Iterable<Variable> {

	/**
	 * The set (array) of variables form the problem (constraint network)
	 */
	private final Variable[] vars;

	/**
	 * The number of the first current future variable, or -1 if no such variable exists.
	 */
	private int first;

	/**
	 * The number of the last current future variable, or -1 if no such variable exists.
	 */
	private int last;

	/**
	 * Backward linking (i.e., from last to first). With i being the number of a variable x, {@code prevs[i]} gives the
	 * number of the variable y that precedes x.
	 */
	private final int[] prevs;

	/**
	 * Forward linking (i.e., from first to last). With i being the number of a variable x, {@code nexts[i]} gives the
	 * number of the variable y that follows x.
	 */
	private final int[] nexts;

	/**
	 * pasts[i] is the ith past variable (valid indexes from 0 to pastTop as in dense set)
	 */
	private final int[] pasts;

	/**
	 * The limit to be used for pasts (as for a dense set)
	 */
	private int pastLimit;

	/**
	 * Builds an object to manage past and future variables, i.e, variables that are, or are not, explicitly assigned by
	 * the solver
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public FutureVariables(Solver solver) {
		this.vars = solver.problem.variables;
		this.first = 0;
		this.last = vars.length - 1;
		this.prevs = IntStream.range(-1, vars.length - 1).toArray();
		this.nexts = IntStream.range(1, vars.length + 1).map(i -> i < vars.length ? i : -1).toArray();
		this.pasts = new int[vars.length];
		this.pastLimit = -1;
		control(Variable.areNumsNormalized(vars));
	}

	/**
	 * Returns the number of future variables, i.e., the number of variables that have not been explicitly assigned by
	 * the solver
	 * 
	 * @return the number of future variables
	 */
	public int size() {
		return vars.length - pastLimit - 1;
	}

	/**
	 * Returns the number of past variables, i.e., the number of variables that have been explicitly assigned by the
	 * solver
	 * 
	 * @return the number of past variables
	 */
	public int nPast() {
		return pastLimit + 1;
	}

	/**
	 * Returns the first future (i.e., not explicitly assigned) variable
	 * 
	 * @return the first future variable
	 */
	public Variable first() {
		return first == -1 ? null : vars[first];
	}

	/**
	 * Returns the future variable that comes after the specified one
	 * 
	 * @param x
	 *            a variable
	 * @return the future variable that comes after the specified one
	 */
	public Variable next(Variable x) {
		assert !x.assigned();
		int e = nexts[x.num];
		return e == -1 ? null : vars[e];
	}

	/**
	 * Returns the last variable that has been assigned, or null
	 * 
	 * @return the last past (i.e., explicitly assigned) variable
	 */
	public Variable lastPast() {
		return pastLimit == -1 ? null : vars[pasts[pastLimit]];
	}

	/**
	 * Returns the ith future variable. BE CAREFUL: this operation is not in O(1).
	 * 
	 * @param i
	 *            the position of the future variable
	 * @return the ith future variable
	 */
	public Variable get(int i) {
		assert 0 <= i && i < size();
		int e = first;
		for (int cnt = 0; cnt < i; cnt++)
			e = nexts[e];
		return vars[e];
	}

	/**
	 * Converts the specified variable from future to past
	 * 
	 * @param x
	 *            the variable to be added
	 */
	public void remove(Variable x) {
		int i = x.num;
		assert IntStream.rangeClosed(0, pastLimit).noneMatch(j -> pasts[j] == i);
		// removing from the list of present elements
		int prev = prevs[i], next = nexts[i];
		if (prev == -1)
			first = next;
		else
			nexts[prev] = next;
		if (next == -1)
			last = prev;
		else
			prevs[next] = prev;
		// adding to the end of the list of absent elements
		pasts[++pastLimit] = i;
	}

	/**
	 * Converts the specified variable from past to future
	 * 
	 * @param x
	 *            the variable to be removed
	 */
	public void add(Variable x) {
		int i = x.num;
		assert pastLimit >= 0 && pasts[pastLimit] == i;
		// removing from the end of the list of absent elements
		pastLimit--;
		// adding to the list of present elements (works only if elements are managed as in a stack)
		int prev = prevs[i], next = nexts[i];
		if (prev == -1)
			first = i;
		else
			nexts[prev] = i;
		if (next == -1)
			last = i;
		else
			prevs[next] = i;
	}

	/**
	 * Calls the specified function (consumer) on each future variable
	 * 
	 * @param consumer
	 *            a function to be called on each future variable
	 */
	public void execute(Consumer<Variable> consumer) {
		for (int e = first; e != -1; e = nexts[e])
			consumer.accept(vars[e]);
	}

	/**
	 * Returns an array with the current future variables
	 * 
	 * @return an array with the current future variables
	 */
	public Variable[] toArray() {
		Variable[] t = new Variable[size()];
		for (int cnt = 0, e = first; e != -1; e = nexts[e])
			t[cnt++] = vars[e];
		return t;
	}

	/**********************************************************************************************
	 * EXPERIMENTAl: iterators for future variables; currently not really exploited (because of strong limitations)
	 *********************************************************************************************/

	private class SimpleIterator implements Iterator<Variable> {

		private int cursor = -1;

		@Override
		public boolean hasNext() {
			return cursor != -1;
		}

		@Override
		public Variable next() {
			if (!hasNext())
				throw new NoSuchElementException();
			Variable x = vars[cursor];
			cursor = nexts[cursor];
			return x;
		}
	}

	private SimpleIterator iterator1 = new SimpleIterator(), iterator2 = new SimpleIterator();

	/**
	 * Such an iterator can only be used for complete iteration (no break and no return accepted)
	 */
	@Override
	public Iterator<Variable> iterator() {
		if (iterator1.cursor == -1) {
			iterator1.cursor = first;
			return iterator1;
		}
		if (iterator2.cursor == -1) {
			iterator2.cursor = first;
			return iterator2;
		}
		System.out.println("CURSORS=" + iterator1.cursor + " " + iterator2.cursor);
		control(false, () -> "Only two nested iterations can only be used for the moment");
		return null;
	}

}
