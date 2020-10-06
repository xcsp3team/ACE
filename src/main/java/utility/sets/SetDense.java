/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package utility.sets;

import java.util.function.Predicate;
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

	public static final int INCREASE_RATIO = 2;
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
		// we build initially a canonical dense set, i.e. a set with values 0, 1, 2 ... (even if this is useful only if initialyFull is true
		// or a sparse set is built)
	}

	public SetDense(int capacity) {
		this(capacity, false);
	}

	public final int first() {
		assert limit >= 0;
		return dense[0];
	}

	public final int last() {
		assert limit >= 0;
		return dense[limit];
	}

	public final int capacity() {
		return dense.length;
	}

	public final int size() {
		return limit + 1;
	}

	public final int free() {
		return dense.length - limit - 1;
	}

	public final int sizeSuchThat(Predicate<Integer> p) {
		return (int) IntStream.rangeClosed(0, limit).filter(i -> p.test(dense[i])).count();
	}

	public final boolean isEmpty() {
		return limit == -1;
	}

	public final boolean isFull() {
		return limit == dense.length - 1;
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

	public void increaseCapacity() {
		dense = IntStream.range(0, capacity() * INCREASE_RATIO).map(i -> i < dense.length ? dense[i] : i).toArray();
	}

	public void clear() {
		limit = -1;
	}

	/**
	 * Be careful: for a dense set, this is not O(1)
	 * 
	 * @param e
	 * @return
	 */
	public boolean isPresent(int e) {
		for (int i = 0; i <= limit; i++)
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

	public final void resetTo(LinkedSet set) {
		assert set.size() <= capacity();
		clear();
		for (int e = set.first(); e != -1; e = set.next(e))
			add(e);
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
		int e = dense[i];
		dense[i] = dense[j];
		dense[j] = e;
	}

	@Override
	public String toString() {
		return "dense={" + IntStream.range(0, size()).mapToObj(i -> dense[i] + "").collect(Collectors.joining(",")) + "}";
	}

	@SuppressWarnings("unused")
	public static void main(String[] args) {
		int mode = Integer.parseInt(args[0]), nValues = Integer.parseInt(args[1]), nIterations = Integer.parseInt(args[2]);
		SetDense set = new SetDense(nValues, true);
		if (mode == 1) {
			for (int cnt = 0; cnt < nIterations; cnt++) {
				for (int i = set.limit; i >= 0; i--) {
					int x = set.dense[i];
					x++;
					// set.dense[0] = x;
				}
			}
		}
		if (mode == 2) {
			int[] dense = set.dense;
			for (int cnt = 0; cnt < nIterations; cnt++) {
				for (int i = set.limit; i >= 0; i--) {
					int x = dense[i];
					x++;
					// dense[0] = x;
				}
			}
		}
		// if (mode == 3) {
		// for (int cnt = 0; cnt < nIterations; cnt++) {
		// for (int v : set) {
		// int x = v;
		// x++;
		// // set.dense[0] = x;
		// }
		// }
		// // for (int v1 : set)
		// // for (int v2 : set)
		// // ;
		// }
		System.out.println(set.dense[0] + " " + set.dense[1]);
	}
}
