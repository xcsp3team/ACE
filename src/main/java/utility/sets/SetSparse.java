/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package utility.sets;

import java.util.Arrays;
import java.util.function.IntFunction;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import utility.Kit;

public class SetSparse extends SetDense {

	public static final SetSparse[] factoryArray(IntFunction<Integer> capacityFunction, int arraySize) {
		return IntStream.range(0, arraySize).mapToObj(i -> new SetSparse(capacityFunction.apply(i))).toArray(SetSparse[]::new);
	}

	public static final SetSparse[] factoryArray(int capacity, int arraySize) {
		return factoryArray(i -> capacity, arraySize);
	}

	public int[] sparse;

	public SetSparse(int capacity, boolean initiallyFull) {
		super(capacity, initiallyFull);
		this.sparse = Kit.range(capacity);
		Kit.control(Arrays.equals(dense, sparse));
	}

	public SetSparse(int capacity) {
		this(capacity, false);
	}

	@Override
	public void increaseCapacity() {
		super.increaseCapacity();
		sparse = IntStream.range(0, dense.length).map(i -> i < sparse.length ? sparse[i] : i).toArray();
		// note that dense.length is the new capacity
	}

	public SetSparse fill() {
		limit = dense.length - 1;
		return this;
	}

	public void resetTo(SetSparse set) {
		Kit.control(this.getClass() == SetSparse.class, () -> "Should only be used with the base class");
		Kit.control(set.capacity() == capacity());
		clear();
		for (int i = 0; i <= set.limit; i++)
			add(set.dense[i]);
	}

	@Override
	public boolean isPresent(int e) {
		return sparse[e] <= limit;
	}

	@Override
	public boolean add(int e) {
		int i = sparse[e];
		if (i <= limit)
			return false; // not added because already present
		limit++;
		if (i > limit) {
			int f = dense[limit];
			dense[i] = f;
			dense[limit] = e;
			sparse[e] = limit;
			sparse[f] = i;
		}
		return true; // added
	}

	@Override
	public void removeAtPosition(int i) {
		assert 0 <= i && i <= limit;
		if (i != limit) {
			int e = dense[i];
			int f = dense[limit];
			dense[i] = f;
			dense[limit] = e;
			sparse[e] = limit;
			sparse[f] = i;
		}
		limit--;
	}

	@Override
	public int shift() {
		assert limit >= 0;
		int e = dense[0];
		if (limit != 0) {
			int f = dense[limit];
			dense[0] = dense[limit];
			dense[limit] = e;
			sparse[e] = limit;
			sparse[f] = 0;
		}
		limit--;
		return e;
	}

	@Override
	public void swapAtPositions(int i, int j) {
		int e = dense[i];
		int f = dense[j];
		dense[i] = f;
		dense[j] = e;
		sparse[e] = j;
		sparse[f] = i;
	}

	public boolean remove(int e) {
		int i = sparse[e];
		if (i > limit)
			return false; // not removed because not present
		if (i != limit) {
			int f = dense[limit];
			dense[i] = f;
			dense[limit] = e;
			sparse[e] = limit;
			sparse[f] = i;
		}
		limit--;
		return true; // removed
	}

	public final void swap(int e, int f) {
		int i = sparse[e];
		int j = sparse[f];
		dense[i] = f;
		dense[j] = e;
		sparse[e] = j;
		sparse[f] = i;
	}

	public final void moveElementsAt(int oldTailLimit) {
		int nSwaps = Math.min(limit + 1, oldTailLimit - limit);
		for (int i = 0; i < nSwaps; i++) {
			int j = oldTailLimit - i;
			int e = dense[i];
			int f = dense[j];
			dense[i] = f;
			dense[j] = e;
			sparse[e] = j;
			sparse[f] = i;
		}

	}

	@Override
	public String toString() {
		return super.toString() + "\nsparse={" + IntStream.range(0, size()).mapToObj(i -> sparse[i] + "").collect(Collectors.joining(",")) + "}";
	}
}
