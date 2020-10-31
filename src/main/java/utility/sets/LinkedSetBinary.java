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

public class LinkedSetBinary implements LinkedSet {

	private static final long[] binaryEmpty = { 0 }, binaryFor0 = { 1 }, binaryFor1 = { 2 }, binaryFor01 = { 3 };

	private static final int[] domainEmpty = {}, domainFor0 = { 0 }, domainFor1 = { 1 }, domainFor01 = { 0, 1 };

	/**
	 * The size of the set number of present elements in the list.
	 */
	protected byte size;

	/**
	 * The last deleted element of the list.
	 */
	protected byte lastRemoved;

	/**
	 * The level at which absent elements have been removed from the list. An array index corresponds to an element. An array value gives
	 * the level at which the corresponding element has been removed from the list. Hence, <code> absentLevels[i] == j </code> means that j
	 * is the removal level of the element i and <code> absentLevels[i] == -1 </code> means that the element i is present.
	 */
	protected int[] removedlevels;

	protected byte mark;

	protected byte[] marks;

	protected int nLevels;

	@Override
	public void finalizeConstruction(int nLevels) {
		this.nLevels = nLevels;
	}

	public LinkedSetBinary() {
		this.size = 2;
		this.lastRemoved = -1;
		this.removedlevels = new int[] { -1, -1 };
		this.mark = -1;
	}

	public LinkedSetBinary(int nLevels) {
		this();
		finalizeConstruction(nLevels);
	}

	@Override
	public int initSize() {
		return 2;
	}

	@Override
	public final int size() {
		return size;
	}

	@Override
	public int nRemoved() {
		return 2 - size;
	}

	@Override
	public final boolean isPresent(int a) {
		return removedlevels[a] == -1;
	}

	@Override
	public int first() {
		return removedlevels[0] == -1 ? 0 : removedlevels[1] == -1 ? 1 : -1;
	}

	@Override
	public int next(int a) {
		return a == 1 ? -1 : removedlevels[1] == -1 ? 1 : -1;
	}

	@Override
	public int last() {
		return removedlevels[1] == -1 ? 1 : removedlevels[0] == -1 ? 0 : -1;
	}

	@Override
	public int prev(int a) {
		return a == 0 ? -1 : removedlevels[0] == -1 ? 0 : -1;
	}

	@Override
	public int get(int i) {
		int a = first();
		for (int cnt = 0; cnt < i; cnt++)
			a = next(a);
		return a;
	}

	@Override
	public int lastRemoved() {
		return lastRemoved;
	}

	/**
	 * Returns the level of the last removed element.
	 */
	@Override
	public int lastRemovedLevel() {
		return lastRemoved == -1 ? -1 : removedlevels[lastRemoved];
	}

	@Override
	public int getRemovedLevelOf(int a) {
		return removedlevels[a];
	}

	@Override
	public boolean isRemovedAtLevel(int a, int level) {
		return removedlevels[a] == level;
	}

	@Override
	public int prevRemoved(int a) {
		return size > 0 || a != lastRemoved ? -1 : lastRemoved == 0 ? 1 : 0;
	}

	@Override
	public void remove(int a, int level) {
		assert (level >= 0 && removedlevels[a] == -1) : "level = " + level + " level = " + removedlevels[a];
		removedlevels[a] = level;
		size--;
		lastRemoved = (byte) a;
	}

	@Override
	public int reduceTo(int a, int level) {
		assert isPresent(a) && level >= 0;
		if (size == 1)
			return 0;
		remove((a == 0 ? 1 : 0), level);
		return 1;
	}

	private void restoreLastDropped() {
		assert removedlevels[lastRemoved] != -1;
		removedlevels[lastRemoved] = -1;
		size++;
		lastRemoved = size == 2 ? -1 : (byte) (lastRemoved == 0 ? 1 : 0);
	}

	@Override
	public void restoreBefore(int level) {
		if (size == 2 || removedlevels[lastRemoved] < level)
			return;
		// if (pseudoProblem != null) pseudoProblem.updateMinBoundAfterAdding(variable, lastAbsent);
		restoreLastDropped();
		if (size == 2 || removedlevels[lastRemoved] < level)
			return;
		// if (pseudoProblem != null) pseudoProblem.updateMinBoundAfterAdding(variable, lastAbsent);
		restoreLastDropped();
	}

	@Override
	public void setMark() {
		assert mark == -1;
		mark = lastRemoved;
	}

	@Override
	public int indexAtMark() {
		return mark;
	}

	@Override
	public void restoreAtMark() {
		for (int e = lastRemoved; e != mark; e = lastRemoved)
			restoreLastDropped();
		mark = -1;
	}

	@Override
	public void setMark(int level) {
		assert marks == null || marks[level] == -1;
		if (marks == null) {
			marks = new byte[nLevels];
			Arrays.fill(marks, (byte) -1);
		}
		marks[level] = lastRemoved;
	}

	@Override
	public void restoreAtMark(int level) {
		for (int e = lastRemoved; e != marks[level]; e = lastRemoved)
			restoreLastDropped();
		marks[level] = -1;
	}

	@Override
	public long[] binaryRepresentation() {
		return size == 2 ? binaryFor01 : size == 0 ? binaryEmpty : removedlevels[1] == -1 ? binaryFor1 : binaryFor0;
	}

	@Override
	public int[] indexes() {
		if (removedlevels[0] == -1)
			return size == 2 ? domainFor01 : domainFor0;
		return size == 1 ? domainFor1 : domainEmpty;
	}

	@Override
	public String stringOfStructures() {
		String s = LinkedSet.super.stringOfStructures();
		StringBuilder sb = new StringBuilder().append("Levels: ");
		for (int lastLevel = -1, i = lastRemoved(); i != -1; i = prevRemoved(i))
			if (removedlevels[i] != lastLevel) {
				sb.append(i + "@" + removedlevels[i] + " ");
				lastLevel = removedlevels[i];
			}
		return s + "\n" + sb.toString();
	}

	@Override
	public boolean controlStructures() {
		return true; // which controls to be done ?
	}
}
