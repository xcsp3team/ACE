/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package sets;

import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class SetDense { // implements Iterable<Integer> {

	// class SimpleIteration implements Iterator<Integer> {
	//
	// private int cursor = -1;
	//
	// @Override
	// public boolean hasNext() {
	// return cursor >= 0;
	// }
	//
	// @Override
	// public Integer next() {
	// return dense[cursor--];
	// }
	//
	// @Override
	// public void remove() {
	// removeElementAtPosition(cursor + 1);// +1 because has been decremented by next()
	// }
	// }
	//
	// private SimpleIteration iteration = new SimpleIteration();
	//
	// @Override
	// public Iterator<Integer> iterator() {
	// Kit.control(iteration.cursor == -1, () -> "Simple (not nested) Iteration can only be used ");
	// iteration.cursor = limit;
	// return iteration;
	// }

	public static final int UNINITIALIZED = -2;

	public int[] dense;

	public int limit;

	protected int mark = UNINITIALIZED;

	public SetDense(int[] dense, boolean initiallyFull) {
		assert !initiallyFull || IntStream.range(0, dense.length).allMatch(i -> IntStream.range(i + 1, dense.length).allMatch(j -> dense[i] != dense[j]));
		this.dense = dense;
		this.limit = initiallyFull ? dense.length - 1 : -1;
	}

	public SetDense(int capacity, boolean initiallyFull) {
		this(IntStream.range(0, capacity).toArray(), initiallyFull);
		// we build initially a canonical dense set, i.e. a set with values 0, 1, 2 ...
		// (even if this is useful only if initialyFull is true or a sparse set is built)
	}

	public SetDense(int capacity) {
		this(capacity, false);
	}

	public void increaseCapacity() {
		dense = IntStream.range(0, capacity() * 2).map(i -> i < dense.length ? dense[i] : i).toArray(); // increase ratio set to 2; hard coding
	}

	public final int capacity() {
		return dense.length;
	}

	public final int size() {
		return limit + 1;
	}

	public final boolean isEmpty() {
		return limit == -1;
	}

	public final boolean isFull() {
		return limit == dense.length - 1;
	}

	public void clear() {
		limit = -1;
	}

	public final int first() {
		assert limit >= 0;
		return dense[0];
	}

	public final int last() {
		return dense[limit];
	}

	public final void setMark() {
		assert mark == UNINITIALIZED;
		mark = limit;
	}

	public final void restoreAtMark() {
		assert mark != UNINITIALIZED;
		limit = mark;
		mark = UNINITIALIZED;
	}

	/**
	 * Be careful: for a dense set, this is not O(1)
	 * 
	 * @param e
	 * @return
	 */
	public boolean isPresent(int e) {
		for (int i = limit; i >= 0; i--)
			if (dense[i] == e)
				return true;
		return false;
	}

	public boolean add(int e) {
		assert !isPresent(e);
		dense[++limit] = e;
		return true;
	}

	/**
	 * Clears the set and add the specified element.
	 * 
	 * @param e
	 */
	public void resetTo(int e) {
		clear();
		add(e);
	}

	/**
	 * Clears the set and add the first nb elements from the specified array.
	 * 
	 * @param elements
	 * @param nb
	 */
	public void resetTo(int[] elements, int nb) {
		clear();
		for (int i = 0; i < nb; i++)
			add(elements[i]);
	}

	public void removeAtPosition(int i) {
		assert 0 <= i && i <= limit;
		int e = dense[i];
		dense[i] = dense[limit];
		dense[limit] = e;
		limit--;
	}

	public int shift() {
		assert limit >= 0;
		int e = dense[0];
		dense[0] = dense[limit];
		dense[limit] = e; // not always necessary (but this is just one instruction)
		limit--;
		return e;
	}

	public int pop() {
		assert limit >= 0;
		limit--;
		return dense[limit + 1];
	}

	public void swapAtPositions(int i, int j) {
		int tmp = dense[i];
		dense[i] = dense[j];
		dense[j] = tmp;
	}

	@Override
	public String toString() {
		return "dense={" + IntStream.range(0, size()).mapToObj(i -> dense[i] + "").collect(Collectors.joining(",")) + "}";
	}

}
