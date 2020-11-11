/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package variables.domains;

import java.util.stream.IntStream;

import variables.Variable;

public final class DomainHugeBounded extends DomainHuge {
	private static final int ASSIGNED = -3;

	private static final int UNITIALIZED = -2;

	private int currValue;

	private int[] limits; // limits[level] gives the index of the first deleted value at level i (or UNITIALIZED if no element has been removed at
							// level i)

	private int lastDeletedLevel; // gives the level of the last dropped element

	private boolean singleton; // true when reduceTo has been called

	@Override
	public void finalizeConstruction(int nLevels) {
		this.limits = IntStream.range(0, nLevels).map(i -> UNITIALIZED).toArray();
	}

	public DomainHugeBounded(Variable var, int firstValue, int lastValue) {
		super(var, firstValue, lastValue);
		this.currValue = firstValue;
		this.lastDeletedLevel = -1;
	}

	@Override
	public int toIdx(int v) {
		return v - firstValue;
	}

	@Override
	public int toVal(int a) {
		return a + firstValue;
	}

	@Override
	public int initSize() {
		return lastValue - firstValue + 1;
	}

	@Override
	public int size() {
		return singleton ? 1 : lastValue - currValue + 1;
	}

	@Override
	public boolean isPresent(int a) {
		assert 0 <= a && a <= last();
		return singleton ? a == currValue - firstValue : a >= (currValue - firstValue);
	}

	@Override
	public int first() {
		assert size() > 0;
		return currValue - firstValue;
	}

	@Override
	public int next(int a) {
		assert first() <= a && a <= last();
		return singleton || a == lastValue - firstValue ? -1 : a + 1;
	}

	@Override
	public int last() {
		assert size() > 0;
		return singleton ? first() : lastValue - firstValue;
	}

	@Override
	public int prev(int a) {
		assert first() <= a && a <= last();
		return singleton || a == currValue - firstValue ? -1 : a - 1;
	}

	@Override
	public int get(int i) {
		assert 0 <= i && i < size();
		return currValue - firstValue + i;
	}

	@Override
	public int lastRemoved() {
		return currValue - firstValue - 1;
	}

	@Override
	public int prevRemoved(int a) {
		assert 0 <= a && a < first();
		return a - 1;
	}

	@Override
	public int lastRemovedLevel() {
		return lastDeletedLevel;
	}

	@Override
	public boolean isRemovedAtLevel(int a, int level) {
		assert 0 <= a && a < first();
		int right = limits[level];
		if (right == UNITIALIZED || a < right - firstValue)
			return false; // no element dropped at this level
		int left = -1;
		for (int j = level + 1; left == -1 && j <= lastDeletedLevel; j++)
			if (limits[j] != UNITIALIZED)
				left = limits[j];
		if (left == -1)
			left = currValue;
		return a < left - firstValue;
	}

	@Override
	public int getRemovedLevelOf(int a) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void remove(int a, int level) {
		assert level >= 0 && a + firstValue == currValue && !singleton : "level = " + level + " present element = " + a;
		if (limits[level] == UNITIALIZED) {
			limits[level] = currValue;
			lastDeletedLevel = level;
		}
		currValue++;
	}

	@Override
	public int reduceTo(int a, int level) {
		assert level >= 0 && a + firstValue == currValue && !singleton;
		if (currValue == lastValue) // the current size is 1
			return 0;
		if (limits[level] == UNITIALIZED) {
			limits[level] = ASSIGNED;
			singleton = true;
			lastDeletedLevel = level;
		}
		return lastValue - currValue;
	}

	@Override
	public void restoreBefore(int level) {
		if (limits[level] == UNITIALIZED)
			return;
		assert currValue > limits[level] && lastDeletedLevel == level;
		if (limits[level] == ASSIGNED) {
			singleton = false;
		} else
			currValue = limits[level];
		limits[level] = UNITIALIZED;
		int i = level - 1;
		while (i >= 0 && limits[i] == UNITIALIZED)
			i--;
		lastDeletedLevel = i;
	}

	@Override
	public Object allValues() {
		throw new UnsupportedOperationException();
	}
}
