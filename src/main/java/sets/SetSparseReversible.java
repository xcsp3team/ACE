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
		sparse = IntStream.range(0, capacity).toArray();
		Kit.control(Arrays.equals(dense, sparse));
	}

	public SetSparseReversible(int capacity, int nLevels) {
		this(capacity, true, nLevels);
	}

	@Override
	public boolean isPresent(int e) {
		return sparse[e] <= limit;
	}

	@Override
	public boolean add(int e) {
		assert !isPresent(e) : sparse[e] + " " + limit;
		int i = sparse[e];
		limit++;
		if (i > limit) {
			int f = dense[limit];
			dense[i] = f;
			dense[limit] = e;
			sparse[f] = i;
			sparse[e] = limit;
		}
		return true;
	}

	public void add(int e, int level) {
		assert !isPresent(e) : sparse[e] + " " + limit;
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		int i = sparse[e];
		limit++;
		if (i > limit) {
			int f = dense[limit];
			dense[i] = f;
			dense[limit] = e;
			sparse[f] = i;
			sparse[e] = limit;
		}
		// add(e); is an alternative to the previous 9 lines
	}

	public void remove(int e) {
		assert isPresent(e) : sparse[e] + " " + limit;
		int i = sparse[e];
		if (i != limit) {
			int f = dense[limit];
			dense[i] = f;
			dense[limit] = e;
			sparse[f] = i;
			sparse[e] = limit;
		}
		limit--;
	}

	public void removeIfPresent(int e) {
		if (sparse[e] <= limit)
			remove(e);
	}

	public void remove(int e, int level) {
		assert isPresent(e) : sparse[e] + " " + limit;
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		int i = sparse[e];
		if (i != limit) {
			int f = dense[limit];
			dense[i] = f;
			dense[limit] = e;
			sparse[f] = i;
			sparse[e] = limit;
		}
		limit--;
		// remove(e); is an alternative to the previous 9 lines
	}

	public void reduceTo(int e, int level) {
		assert isPresent(e) : sparse[e] + " " + limit;
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		int i = sparse[e];
		if (i != 0) {
			int f = dense[0];
			dense[i] = f;
			dense[0] = e;
			sparse[f] = i;
			sparse[e] = 0;
		}
		limit = 0;
	}

	@Override
	public void removeAtPosition(int i, int level) {
		assert 0 <= i && i <= limit;
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		if (i != limit) {
			int e = dense[i];
			int f = dense[limit];
			dense[i] = f;
			dense[limit] = e;
			sparse[f] = i;
			sparse[e] = limit;
		}
		limit--;
		// remove(dense[i]); is an alternative to the previous 9 lines
	}

	@Override
	public void swapAtPositions(int i, int j) {
		int e = dense[i];
		int f = dense[j];
		dense[i] = f;
		dense[j] = e;
		sparse[f] = i;
		sparse[e] = j;
	}

}
