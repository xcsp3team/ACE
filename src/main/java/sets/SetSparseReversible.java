/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package sets;

import java.util.Arrays;
import java.util.stream.IntStream;

import utility.Kit;

/**
 * for sparse sets, dense values are necessarily 0, 1, ... capacity-1, and dense[sparse[value]] = value
 */
public class SetSparseReversible extends SetDenseReversible {
	public int[] sparse;

	public SetSparseReversible(int capacity, boolean initiallyFull, int nLevels) {
		super(capacity, initiallyFull, nLevels);
		this.sparse = IntStream.range(0, capacity).toArray();
		Kit.control(Arrays.equals(dense, sparse));
	}

	public SetSparseReversible(int capacity, int nLevels) {
		this(capacity, true, nLevels);
	}

	@Override
	public boolean isPresent(int a) {
		return sparse[a] <= limit;
	}

	@Override
	public boolean add(int a) {
		assert !isPresent(a) : sparse[a] + " " + limit;
		int i = sparse[a];
		limit++;
		if (i > limit) {
			int b = dense[limit];
			dense[i] = b;
			dense[limit] = a;
			sparse[b] = i;
			sparse[a] = limit;
		}
		return true;
	}

	public void add(int a, int level) {
		assert !isPresent(a) : sparse[a] + " " + limit;
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		int i = sparse[a];
		limit++;
		if (i > limit) {
			int b = dense[limit];
			dense[i] = b;
			dense[limit] = a;
			sparse[b] = i;
			sparse[a] = limit;
		}
		// add(e); is an alternative to the previous 9 lines
	}

	public void remove(int a) {
		assert isPresent(a) : sparse[a] + " " + limit;
		int i = sparse[a];
		if (i != limit) {
			int b = dense[limit];
			dense[i] = b;
			dense[limit] = a;
			sparse[b] = i;
			sparse[a] = limit;
		}
		limit--;
	}

	public void removeIfPresent(int a) {
		if (sparse[a] <= limit)
			remove(a);
	}

	public void remove(int a, int level) {
		assert isPresent(a) : sparse[a] + " " + limit;
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		int i = sparse[a];
		if (i != limit) {
			int b = dense[limit];
			dense[i] = b;
			dense[limit] = a;
			sparse[b] = i;
			sparse[a] = limit;
		}
		limit--;
		// remove(e); is an alternative to the previous 9 lines
	}

	public void reduceTo(int a, int level) {
		assert isPresent(a) : sparse[a] + " " + limit;
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		int i = sparse[a];
		if (i != 0) {
			int b = dense[0];
			dense[i] = b;
			dense[0] = a;
			sparse[b] = i;
			sparse[a] = 0;
		}
		limit = 0;
	}

	@Override
	public void removeAtPosition(int i, int level) {
		assert 0 <= i && i <= limit;
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		if (i != limit) {
			int a = dense[i];
			int b = dense[limit];
			dense[i] = b;
			dense[limit] = a;
			sparse[b] = i;
			sparse[a] = limit;
		}
		limit--;
		// remove(dense[i]); is an alternative to the previous 9 lines
	}

	@Override
	public void swapAtPositions(int i, int j) {
		int a = dense[i];
		int b = dense[j];
		dense[i] = b;
		dense[j] = a;
		sparse[b] = i;
		sparse[a] = j;
	}

}
