/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package utility.sets;

import java.util.stream.IntStream;

import org.xcsp.common.Constants;

import utility.Kit;
import utility.exceptions.MissingImplementationException;

public final class LinkedSetUnordered implements LinkedSet {

	private static final int UNITIALIZED = -2;

	private int[] sparse;

	private int[] dense;

	private int initLimit; // corresponds to the index of the last present element at time of construction

	private int limit; // corresponds to the index of the last present element

	private int[] limits; // limits[level] gives the position of the first deleted element at level i (or UNITIALIZED if no element has been removed
							// at level i)

	private int currLevel; // gives the level of the last dropped element

	private int positionOfLastMovedElement;

	protected int mark;

	protected int[] marks;

	private int markLevel;

	private int[] markLevels;

	protected int nLevels;

	@Override
	public void finalizeConstruction(int nLevels) {
		this.nLevels = nLevels;
		this.limits = IntStream.range(0, nLevels).map(i -> UNITIALIZED).toArray();
		this.initLimit = limit; // useful if some values have been deleted at construction time
	}

	public LinkedSetUnordered(int initSize) {
		Kit.control(0 < initSize && initSize <= Constants.MAX_SAFE_INT, () -> "Pb with initSize=" + initSize);
		this.sparse = Kit.range(initSize);
		this.dense = Kit.range(initSize);
		this.initLimit = sparse.length - 1;
		this.limit = sparse.length - 1;
		this.currLevel = -1;
		this.mark = -1;
	}

	public LinkedSetUnordered(int initSize, int nLevels) {
		this(initSize);
		finalizeConstruction(nLevels);
	}

	@Override
	public int initSize() {
		return dense.length;
	}

	@Override
	public int size() {
		return limit + 1;
	}

	@Override
	public boolean isPresent(int a) {
		return sparse[a] <= limit;
	}

	@Override
	public int first() {
		return limit == -1 ? -1 : dense[0];
	}

	@Override
	public int next(int a) {
		int i = sparse[a];
		if (i < limit)
			return dense[i + 1];
		if (i == limit + 1)
			return positionOfLastMovedElement == i ? -1 : dense[positionOfLastMovedElement];
		// the element has just been removed and replaced at its last position by an element not considered yet (except if
		// positionOfLastDroppedElement = i).
		assert i == limit;
		return -1;
	}

	@Override
	public int last() {
		return limit == -1 ? -1 : dense[limit];
	}

	@Override
	public int prev(int a) {
		int i = sparse[a];
		if (i == 0)
			return -1;
		if (i == limit + 1)
			return positionOfLastMovedElement == 0 ? -1 : dense[positionOfLastMovedElement - 1];
		// the element has just been removed and replaced at its last position by an element already considered.
		assert i <= limit;
		return dense[i - 1];
	}

	@Override
	public int get(int i) {
		return dense[i];
	}

	@Override
	public int lastRemoved() {
		if (limit == initLimit)
			return -1;
		assert limit < initLimit;
		return dense[limit + 1];
	}

	@Override
	public int prevRemoved(int a) {
		int i = sparse[a];
		if (i == initLimit)
			return -1;
		assert !isPresent(a) && limit < i && i < initLimit;
		return dense[i + 1];
	}

	@Override
	public int lastRemovedLevel() {
		return currLevel;
	}

	@Override
	public boolean isRemovedAtLevel(int a, int level) {
		if (limits[level] == UNITIALIZED)
			return false; // no element dropped at this level
		int i = sparse[a];
		if (limits[level] < i)
			return false; // because dropped before the level
		int left = -1;
		for (int j = level + 1; left == -1 && j <= currLevel; j++)
			if (limits[j] != UNITIALIZED)
				left = limits[j];
		return left < i;
	}

	@Override
	public int getRemovedLevelOf(int a) {
		throw new MissingImplementationException();
	}

	private void swap(int i, int j) {
		int e = dense[i];
		int f = dense[j];
		dense[i] = f;
		dense[j] = e;
		sparse[e] = j;
		sparse[f] = i;
	}

	@Override
	public void remove(int a, int level) {
		assert level >= 0 && isPresent(a) : "level = " + level + " present element = " + a;
		if (limits[level] == UNITIALIZED) {
			limits[level] = limit;
			currLevel = level;
		}
		positionOfLastMovedElement = sparse[a];
		if (positionOfLastMovedElement != limit)
			swap(positionOfLastMovedElement, limit);
		limit--;
		assert controlStructures();
	}

	@Override
	public int reduceTo(int a, int level) {
		assert level >= 0 && isPresent(a);
		if (limit == 0) // the current size is 1
			return 0;
		if (limits[level] == UNITIALIZED) {
			limits[level] = limit;
			currLevel = level;
		}
		int limitBefore = limit;
		// swap between element and element at position 0
		positionOfLastMovedElement = sparse[a];
		if (positionOfLastMovedElement != 0)
			swap(0, positionOfLastMovedElement);
		limit = 0;
		return limitBefore;
	}

	@Override
	public void restoreBefore(int level) {
		if (limits[level] == UNITIALIZED)
			return;
		assert limit < limits[level] && currLevel == level;
		limit = limits[level];
		limits[level] = UNITIALIZED;
		int i = level - 1;
		while (i >= 0 && limits[i] == UNITIALIZED)
			i--;
		currLevel = i;
		assert controlStructures();
	}

	@Override
	public void setMark() {
		// assert mark == -1
		mark = limit;
		markLevel = currLevel;
	}

	@Override
	public void restoreAtMark() {
		limit = mark;
		for (int i = currLevel; i > markLevel; i--)
			limits[i] = UNITIALIZED;
		currLevel = markLevel;
		mark = -1;
		// if (positionOfLastMovedElement != 0)
		// swap(0, positionOfLastMovedElement);
	}

	@Override
	public void setMark(int level) {
		assert marks == null || marks[level] == -1;
		if (marks == null) {
			marks = Kit.repeat(-1, nLevels);
			markLevels = Kit.repeat(-1, nLevels);
		}
		marks[level] = limit;
		markLevels[level] = currLevel;
	}

	@Override
	public void restoreAtMark(int level) {
		limit = marks[level];
		for (int i = currLevel; i > markLevels[level]; i--)
			limits[i] = UNITIALIZED;
		currLevel = markLevels[level];
		marks[level] = -1;
	}

	@Override
	public int indexAtMark() {
		return mark == -1 ? -1 : dense[mark]; // m;
	}

	@Override
	public long[] binaryRepresentation() {
		return null;
	}

	@Override
	public int[] indexes() {
		return IntStream.range(0, size()).map(i -> dense[i]).toArray();
	}

	@Override
	public String stringOfStructures() {
		String s = LinkedSet.super.stringOfStructures();
		StringBuilder sb = new StringBuilder().append("Levels: ");
		for (int i = currLevel; i >= 0; i--)
			if (limits[i] != UNITIALIZED)
				sb.append(dense[limits[i]] + "@" + i + " ");
		return s + "\n" + sb.toString();
	}

	@Override
	public boolean controlStructures() {
		if (IntStream.range(0, sparse.length).anyMatch(i -> dense[sparse[i]] != i)
				|| IntStream.range(currLevel + 1, limits.length).anyMatch(i -> limits[i] != UNITIALIZED))
			return false;
		for (int last = Integer.MAX_VALUE, i = 0; i <= currLevel; i++)
			if (limits[i] != UNITIALIZED) {
				if (limits[i] >= last)
					return false;
				last = limits[i];
			}
		return true;
	}
}
