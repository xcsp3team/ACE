/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package sets;

import java.util.Arrays;

/**
 * This class implements the interface SetLinked for sets containing only two elements (indexes 0 and 1).
 * 
 * @author Christophe Lecoutre
 */
public class SetLinkedBinary implements SetLinked {

	private static final long[] binaryEmpty = { 0 }, binaryFor0 = { 1 }, binaryFor1 = { 2 }, binaryFor01 = { 3 };

	/**
	 * The size of the set (i.e., the current number of elements)
	 */
	private byte size;

	/**
	 * The last deleted element (index) of the set.
	 */
	private byte lastRemoved;

	/**
	 * The level at which absent elements (indexes) have been removed from the set. Hence, <code> removedLevels[a] == i </code> means that i is the removal
	 * level of the index a and <code> removedLevels[a] == -1 </code> means that the index a is still present.
	 */
	private int[] removedlevels;

	private byte mark;

	private byte[] marks;

	private int nLevels;

	@Override
	public final void setNumberOfLevels(int nLevels) {
		this.nLevels = nLevels;
	}

	public SetLinkedBinary() {
		this.size = 2;
		this.lastRemoved = -1;
		this.removedlevels = new int[] { -1, -1 };
		this.mark = -1;
	}

	@Override
	public final int initSize() {
		return 2;
	}

	@Override
	public final int size() {
		return size;
	}

	@Override
	public final int nRemoved() {
		return 2 - size;
	}

	@Override
	public final boolean contains(int a) {
		return removedlevels[a] == -1;
	}

	@Override
	public final int first() {
		return removedlevels[0] == -1 ? 0 : removedlevels[1] == -1 ? 1 : -1;
	}

	@Override
	public final int next(int a) {
		return a == 1 ? -1 : removedlevels[1] == -1 ? 1 : -1;
	}

	@Override
	public final int last() {
		return removedlevels[1] == -1 ? 1 : removedlevels[0] == -1 ? 0 : -1;
	}

	@Override
	public final int prev(int a) {
		return a == 0 ? -1 : removedlevels[0] == -1 ? 0 : -1;
	}

	@Override
	public final int lastRemoved() {
		return lastRemoved;
	}

	@Override
	public final int lastRemovedLevel() {
		return lastRemoved == -1 ? -1 : removedlevels[lastRemoved];
	}

	@Override
	public final int removedLevelOf(int a) {
		return removedlevels[a];
	}

	@Override
	public final int prevRemoved(int a) {
		return size > 0 || a != lastRemoved ? -1 : lastRemoved == 0 ? 1 : 0;
	}

	@Override
	public final void remove(int a, int level) {
		assert (level >= 0 && removedlevels[a] == -1) : "level = " + level + " level = " + removedlevels[a];
		removedlevels[a] = level;
		size--;
		lastRemoved = (byte) a;
	}

	@Override
	public final int reduceTo(int a, int level) {
		assert contains(a) && level >= 0;
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
	public final void restoreBefore(int level) {
		if (size == 2 || removedlevels[lastRemoved] < level)
			return;
		restoreLastDropped();
		if (size == 2 || removedlevels[lastRemoved] < level)
			return;
		restoreLastDropped();
	}

	@Override
	public final void setMark() {
		assert mark == -1;
		mark = lastRemoved;
	}

	@Override
	public final int getMark() {
		return mark;
	}

	@Override
	public final void restoreAtMark() {
		for (int e = lastRemoved; e != mark; e = lastRemoved)
			restoreLastDropped();
		mark = -1;
	}

	@Override
	public final void setMark(int level) {
		assert marks == null || marks[level] == -1;
		if (marks == null) {
			marks = new byte[nLevels];
			Arrays.fill(marks, (byte) -1);
		}
		marks[level] = lastRemoved;
	}

	@Override
	public final void restoreAtMark(int level) {
		for (int e = lastRemoved; e != marks[level]; e = lastRemoved)
			restoreLastDropped();
		marks[level] = -1;
	}

	@Override
	public final long[] binary() {
		return size == 2 ? binaryFor01 : size == 0 ? binaryEmpty : removedlevels[1] == -1 ? binaryFor1 : binaryFor0;
	}

	@Override
	public final String stringOfStructures() {
		String s = SetLinked.super.stringOfStructures();
		StringBuilder sb = new StringBuilder().append("Levels: ");
		for (int lastLevel = -1, i = lastRemoved(); i != -1; i = prevRemoved(i))
			if (removedlevels[i] != lastLevel) {
				sb.append(i + "@" + removedlevels[i] + " ");
				lastLevel = removedlevels[i];
			}
		return s + "\n" + sb.toString();
	}
}
