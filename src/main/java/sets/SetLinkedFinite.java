/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package sets;

import static utility.Kit.control;

import java.util.Arrays;
import java.util.stream.IntStream;

import org.xcsp.common.Constants;

import utility.Bit;
import utility.Kit;

/**
 * This class implements the interface LinkedSet for ordered sets containing a finite number of elements (indexes).
 * 
 * @author Christophe Lecoutre
 */
public class SetLinkedFinite implements SetLinked {

	/**
	 * The number of present elements (indexes).
	 */
	protected int size;

	/**
	 * The first (present) index.
	 */
	protected int first;

	/**
	 * The last (present) index.
	 */
	protected int last;

	/**
	 * The backward linking of all present indexes of the list (from last to first). Hence, <code> prevs[a] == b </code>
	 * means that b is the previous present index in the list before a, or -1 if there is none..
	 */
	private final int[] prevs;

	/**
	 * The forward linking of all present indexes of the list (from first to last). Hence, <code> nexts[a] == b </code>
	 * means that b is the next present index in the list after a, or -1 if there is none.
	 */
	private final int[] nexts;

	/**
	 * The last dropped index of the list.
	 */
	protected int lastRemoved;

	/**
	 * The backward linking of all absent indexes of the list (from last to first). Hence,
	 * <code> prevRemoved[a] == b </code> means that b is the previously deleted index of the list before a, or -1 if
	 * there is none.
	 */
	private final int[] prevRemoved;

	/**
	 * The level at which absent indexes have been removed from the list. Hence, <code> removedLevels[a] == i </code>
	 * means that i is the removal level of the index a and <code> removedLevels[a] == -1 </code> means that the index a
	 * is still present.
	 */
	public final int[] removedLevels;

	protected int mark;

	protected int[] marks;

	protected int nLevels;

	@Override
	public void setNumberOfLevels(int nLevels) {
		this.nLevels = nLevels;
		this.lastRemoved = -1; // useful if some values have been deleted at construction time
	}

	/**
	 * Builds a finite linked set of the specified initial size
	 * 
	 * @param initSize
	 *            the initial size of the set
	 */
	public SetLinkedFinite(int initSize) {
		control(0 < initSize && initSize <= Constants.MAX_SAFE_INT, () -> "capacity=" + initSize);
		this.size = initSize;
		this.first = 0;
		this.last = initSize - 1;
		this.prevs = IntStream.range(0, initSize).map(i -> i - 1).toArray();
		this.nexts = IntStream.range(0, initSize).map(i -> i < initSize - 1 ? i + 1 : -1).toArray();
		this.lastRemoved = -1;
		this.prevRemoved = Kit.repeat(-1, initSize); // Kit.repeat((short) -1, initialSize);
		this.removedLevels = Kit.repeat(-1, initSize);
		this.mark = -1;
	}

	@Override
	public int initSize() {
		return prevs.length;
	}

	@Override
	public final int size() {
		return size;
	}

	@Override
	public final boolean contains(int a) {
		return removedLevels[a] == -1;
	}

	@Override
	public  int first() {
		return first;
	}

	@Override
	public int next(int a) {
		if (removedLevels[a] == -1)
			return nexts[a];
		// below a can not be equal to first since a is not present
		if (a < first)
			return first;
		int next = nexts[a];
		if (next == -1 || next > last)
			return -1;
		while (removedLevels[next] != -1)
			next = nexts[next];
		return next;
	}

	@Override
	public  int last() {
		return last;
	}

	@Override
	public int prev(int a) {
		if (removedLevels[a] == -1)
			return prevs[a];
		// below a can not be equal to last since a is not present
		if (a > last)
			return last;
		int prev = prevs[a];
		if (prev < first) // includes prev == -1
			return -1;
		while (removedLevels[prev] != -1)
			prev = prevs[prev];
		return prev;
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
		return lastRemoved == -1 ? -1 : removedLevels[lastRemoved];
	}

	@Override
	public int removedLevelOf(int a) {
		return removedLevels[a];
	}

	@Override
	public int prevRemoved(int a) {
		return prevRemoved[a];
	}

	protected void removeElement(int a) {
		// remove from the list of present elements
		int prev = prevs[a], next = nexts[a];
		if (prev == -1)
			first = next;
		else
			nexts[prev] = next;
		if (next == -1)
			last = prev;
		else
			prevs[next] = prev;
		// add to the end of the list of absent elements
		prevRemoved[a] = lastRemoved;
		lastRemoved = a;
	}

	@Override
	public final void remove(int a, int level) {
		assert contains(a) && level >= 0 : "level = " + level + " absentLevel = " + removedLevels[a];
		removedLevels[a] = level;
		size--;
		removeElement(a);
	}

	@Override
	public int reduceTo(int a, int level) {
		assert contains(a) && level >= 0;
		int sizeBefore = size;
		for (int b = first; b != -1; b = next(b))
			if (b != a)
				remove(b, level);
		return sizeBefore - size;
	}

	protected void addElement(int a) {
		assert lastRemoved == a;
		// add to the list of present elements (works only if elements are managed as in a stack)
		int prev = prevs[a], next = nexts[a];
		if (prev == -1)
			first = a;
		else
			nexts[prev] = a;
		if (next == -1)
			last = a;
		else
			prevs[next] = a;
		// remove from the list of absent elements
		lastRemoved = prevRemoved[a];
	}

	private void restoreLastDropped() {
		assert lastRemoved != -1 && !contains(lastRemoved);
		removedLevels[lastRemoved] = -1;
		size++;
		addElement(lastRemoved);
	}

	@Override
	public void restoreBefore(int level) {
		assert lastRemoved == -1 || removedLevels[lastRemoved] <= level;
		for (int a = lastRemoved; a != -1 && removedLevels[a] >= level; a = lastRemoved)
			restoreLastDropped();
	}

	@Override
	public void setMark() {
		assert mark == -1;
		mark = lastRemoved;
	}

	@Override
	public int getMark() {
		return mark;
	}

	@Override
	public void restoreAtMark() {
		for (int a = lastRemoved; a != mark; a = lastRemoved)
			restoreLastDropped();
		mark = -1;
	}

	@Override
	public void setMark(int level) {
		assert marks == null || marks[level] == -1;
		if (marks == null)
			marks = Kit.repeat(-1, nLevels);
		marks[level] = lastRemoved;
	}

	@Override
	public void restoreAtMark(int level) {
		for (int a = lastRemoved; a != marks[level]; a = lastRemoved)
			restoreLastDropped();
		marks[level] = -1;
	}

	@Override
	public String stringOfStructures() {
		String s = SetLinked.super.stringOfStructures();
		StringBuilder sb = new StringBuilder().append("Levels: ");
		for (int lastLevel = -1, a = lastRemoved(); a != -1; a = prevRemoved(a))
			if (removedLevels[a] != lastLevel) {
				sb.append(a + "@" + removedLevels[a] + " ");
				lastLevel = removedLevels[a];
			}
		return s + "\n" + sb.toString();
	}

	@Override
	public boolean controlStructures() {
		int cnt = 0;
		for (int a = first; a != -1; a = nexts[a]) {
			if (removedLevels[a] != -1 || nexts[a] != -1 && a >= nexts[a]) {
				Kit.log.info("pb forward present : absent = " + removedLevels[a] + " i= " + a + " next = " + nexts[a]);
				return false;
			}
			cnt++;
		}
		control(cnt == size(), () -> "pb nb elements " + size());
		for (int a = last; a != -1; a = prevs[a])
			if (removedLevels[a] != -1 || prevs[a] != -1 && a <= prevs[a]) {
				Kit.log.info("pb backward present : absent = " + removedLevels[a] + " i= " + a + " prev = " + prevs[a]);
				return false;
			}
		for (int a = lastRemoved; a != -1; a = prevRemoved[a]) {
			control(removedLevels[a] != -1, () -> "bad value of absentLevels");
			if (prevRemoved[a] != -1 && removedLevels[prevRemoved[a]] > removedLevels[a]) {
				Kit.log.info("level of " + a + " = " + removedLevels[a] + " level of " + prevRemoved[a] + " = " + removedLevels[prevRemoved[a]]);
				return false;
			}
		}
		return true;
	}

	public static class SetLinkedFiniteWithBits extends SetLinkedFinite {

		protected long[] binaryRepresentation;

		@Override
		public long[] binary() {
			return binaryRepresentation;
		}

		public SetLinkedFiniteWithBits(int initSize) {
			super(initSize);
			binaryRepresentation = new long[initSize / Long.SIZE + (initSize % Long.SIZE != 0 ? 1 : 0)];
			Arrays.fill(binaryRepresentation, Bit.ALL_LONG_BITS_TO_1);
			binaryRepresentation[binaryRepresentation.length - 1] = Bit.bitsAt1To(initSize - ((binaryRepresentation.length - 1) * Long.SIZE));
		}

		@Override
		protected void addElement(int a) {
			super.addElement(a);
			binaryRepresentation[a / Long.SIZE] |= Bit.ONE_LONG_BIT_TO_1[a % Long.SIZE];
			// binaryRepresentation[element >> 6] |= Bit.ONE_LONG_BIT_TO_1[element & ((1 << 6) - 1)];
		}

		@Override
		protected void removeElement(int a) {
			super.removeElement(a);
			binaryRepresentation[a / Long.SIZE] &= Bit.ONE_LONG_BIT_TO_0[a % Long.SIZE];
			// binaryRepresentation[element >> 6] &= Bit.ONE_LONG_BIT_TO_0[element & ((1 << 6) - 1)];
		}
	}

	public static final class SetLinkedFiniteWithBits2 extends SetLinkedFiniteWithBits {

		public final SetSparse set;

		public SetLinkedFiniteWithBits2(int initSize) {
			super(initSize);
			this.set = new SetSparse(binaryRepresentation.length, true);
		}

		@Override
		protected void addElement(int a) {
			super.addElement(a);
			set.add(a / Long.SIZE);
		}

		@Override
		protected void removeElement(int a) {
			super.removeElement(a);
			int i = a / Long.SIZE;
			if (binaryRepresentation[i] == 0)
				set.remove(i);
		}
	}

}