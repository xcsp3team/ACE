/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package solver;

import java.util.Iterator;
import java.util.function.Consumer;
import java.util.stream.IntStream;

import utility.Kit;
import variables.Variable;

/**
 * This abstract class allows us to manage past and future variables. It is used by solvers.
 */
public final class FutureVariables implements Iterable<Variable> {

	private class SimpleIterator implements Iterator<Variable> {

		private int cursor = -1;

		@Override
		public boolean hasNext() {
			return cursor != -1;
		}

		@Override
		public Variable next() {
			Variable x = vars[cursor];
			cursor = nexts[cursor];
			return x;
		}
	}

	private SimpleIterator iterator1 = new SimpleIterator(), iterator2 = new SimpleIterator();

	@Override
	/**
	 * Such an iterator can only be used for complete iteration (no break and no return accepted)
	 */
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
		Kit.control(false, () -> "Only two nested iterations can only be used for the moment");
		return null;
	}

	/**
	 * The number of the first current future variable, or -1 if no such variable exists.
	 */
	public int first;

	/**
	 * The number of the last current future variable, or -1 if no such variable exists.
	 */
	public int last;

	/**
	 * Backward linking (i.e., from last to first). With i being the number of a variable x, {@code prevs[i]} gives the number of the variable y that precedes
	 * x.
	 */
	public final int[] prevs;

	/**
	 * Forward linking (i.e., from first to last). With i being the number of a variable x, {@code nexts[i]} gives the number of the variable y that follows x.
	 */
	public final int[] nexts;

	public final int[] pasts;

	public int pastTop;

	private final Variable[] vars;

	public FutureVariables(Variable[] vars) {
		this.first = 0;
		this.last = vars.length - 1;
		this.prevs = IntStream.range(-1, vars.length - 1).toArray();
		this.nexts = IntStream.range(1, vars.length + 1).map(i -> i < vars.length ? i : -1).toArray();
		this.pasts = new int[vars.length];
		this.pastTop = -1;
		this.vars = vars;
		Kit.control(Variable.areNumsNormalized(vars));
	}

	public int size() {
		return vars.length - pastTop - 1;
	}

	/**
	 * Returns the number of past variables, i.e., the number of variables which have been explicitly assigned by the solver.
	 */
	public int nDiscarded() {
		return pastTop + 1;
	}

	/**
	 * Returns {@code true} if the specified element (number of variable) is currently present (i.e., if the associated variable is currently future). BE
	 * CAREFUL: this operation is not in O(1).
	 * 
	 * @param e
	 *            the number of a variable
	 * @return {@code true} if the specified element (number of variable) is currently present
	 */
	public boolean isPresent(int e) {
		return IntStream.rangeClosed(0, pastTop).noneMatch(i -> pasts[i] == e);
	}

	private void pop() {
		assert pastTop >= 0;
		int e = pasts[pastTop--];
		// add to the list of present elements (works only if elements are managed as in a stack)
		int prev = prevs[e], next = nexts[e];
		if (prev == -1)
			first = e;
		else
			nexts[prev] = e;
		if (next == -1)
			last = e;
		else
			prevs[next] = e;
	}

	private void push(int e) {
		assert isPresent(e);
		// remove from the list of present elements
		int prev = prevs[e], next = nexts[e];
		if (prev == -1)
			first = next;
		else
			nexts[prev] = next;
		if (next == -1)
			last = prev;
		else
			prevs[next] = prev;
		// add to the end of the list of absent elements
		pasts[++pastTop] = e;
	}

	public Variable first() {
		return first == -1 ? null : vars[first];
	}

	/**
	 * Returns the next future variable after the variable given in parameter.
	 */
	public Variable next(Variable x) {
		assert x.isFuture();
		int e = nexts[x.num];
		return e == -1 ? null : vars[e];
	}

	/**
	 * BE CAREFUL: this operation is not in O(1).
	 * 
	 * @param i
	 * @return
	 */
	public Variable get(int i) {
		assert 0 <= i && i < size();
		int e = first;
		for (int cnt = 0; cnt < i; cnt++)
			e = nexts[e];
		return vars[e];
	}

	/**
	 * Returns the last variable that has been assigned.
	 */
	public Variable lastPast() {
		return pastTop == -1 ? null : vars[pasts[pastTop]];
	}

	/**
	 * This method is called in order to convert the given variable from future to past.
	 */
	public void add(Variable x) {
		push(x.num);
	}

	/**
	 * This method is called in order to convert the given variable from past to future.
	 */
	public void remove(Variable x) {
		assert pastTop >= 0 && x.num == pasts[pastTop];
		pop();
	}

	public void execute(Consumer<Variable> consumer) {
		for (int e = first; e != -1; e = nexts[e])
			consumer.accept(vars[e]);
	}

	public Variable[] toArray() {
		Variable[] t = new Variable[size()];
		for (int cnt = 0, e = first; e != -1; e = nexts[e])
			t[cnt++] = vars[e];
		return t;
	}

}
