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

import org.xcsp.common.Constants;

import utility.Bit;
import utility.Kit;

public class LinkedSetOrdered implements LinkedSet {
	/**
	 * The number of present elements in the list.
	 */
	protected int size;

	/**
	 * The first (present) element of the list.
	 */
	protected int first;

	/**
	 * The last (present) element of the list.
	 */
	protected int last;

	/**
	 * The backward linking of all present elements of the list (from last to first). An array index corresponds to an element. An array value gives the
	 * previous present element of the list or -1 if it does not exist. Hence, <code> prevs[i] == j </code> means that j is the previous present element in the
	 * list before i.
	 */
	private final int[] prevs;

	/**
	 * The forward linking of all present elements of the list (from first to last). An array index corresponds to an element. An array value gives the next
	 * present element of the list or -1 if it does not exist. Hence, <code> nexts[i] == j </code> means that j is the next present element in the list after i.
	 */
	private final int[] nexts;

	/**
	 * The last dropped element of the list.
	 */
	protected int lastRemoved;

	/**
	 * The backward linking of all absent elements of the list (from last to first). An array index corresponds to an element. An array value gives the previous
	 * absent element of the list or -1 if it does not exist. Hence, <code> prevsDel[i] == j </code> means that j is the previously deleted element of the list
	 * before i.
	 */
	private final int[] prevRemoved;

	/**
	 * The level at which absent elements have been removed from the list. An array index corresponds to an element. An array value gives the level at which the
	 * corresponding element has been removed from the list. Hence, <code> absentLevels[i] == j </code> means that j is the removal level of the element i and
	 * <code> removedLevels[i] == -1 </code> means that the element i is present.
	 */
	private final int[] removedLevels;

	protected int mark;

	protected int[] marks;

	protected int nLevels;

	@Override
	public void finalizeConstruction(int nLevels) {
		this.nLevels = nLevels;
		this.lastRemoved = -1; // useful if some values have been deleted at construction time
	}

	public LinkedSetOrdered(int initSize) {
		Kit.control(0 < initSize && initSize <= Constants.MAX_SAFE_INT, () -> "capacity=" + initSize);
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

	public LinkedSetOrdered(int initSize, int nLevels) {
		this(initSize);
		finalizeConstruction(nLevels);
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
	public final boolean isPresent(int a) {
		return removedLevels[a] == -1;
	}

	@Override
	public final int first() {
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
	public final int last() {
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
	public void remove(int a, int level) {
		assert isPresent(a) && level >= 0 : "level = " + level + " absentLevel = " + removedLevels[a];
		removedLevels[a] = level;
		size--;
		removeElement(a);
	}

	@Override
	public int reduceTo(int a, int level) {
		assert isPresent(a) && level >= 0;
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
		assert lastRemoved != -1 && !isPresent(lastRemoved);
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
	public int indexAtMark() {
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
	public long[] binary() {
		return null;
	}

	@Override
	public String stringOfStructures() {
		String s = LinkedSet.super.stringOfStructures();
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
		Kit.control(cnt == size(), () -> "pb nb elements " + size());
		for (int a = last; a != -1; a = prevs[a])
			if (removedLevels[a] != -1 || prevs[a] != -1 && a <= prevs[a]) {
				Kit.log.info("pb backward present : absent = " + removedLevels[a] + " i= " + a + " prev = " + prevs[a]);
				return false;
			}
		for (int a = lastRemoved; a != -1; a = prevRemoved[a]) {
			Kit.control(removedLevels[a] != -1, () -> "bad value of absentLevels");
			if (prevRemoved[a] != -1 && removedLevels[prevRemoved[a]] > removedLevels[a]) {
				Kit.log.info("level of " + a + " = " + removedLevels[a] + " level of " + prevRemoved[a] + " = " + removedLevels[prevRemoved[a]]);
				return false;
			}
		}
		return true;
	}

	public static class LinkedSetOrderedWithBits extends LinkedSetOrdered {

		protected long[] binaryRepresentation;

		@Override
		public long[] binary() {
			return binaryRepresentation;
		}

		public LinkedSetOrderedWithBits(int initSize) {
			super(initSize);
			binaryRepresentation = new long[initSize / Long.SIZE + (initSize % Long.SIZE != 0 ? 1 : 0)];
			Arrays.fill(binaryRepresentation, Bit.ALL_LONG_BITS_TO_1);
			binaryRepresentation[binaryRepresentation.length - 1] = Bit.bitsA1To(initSize - ((binaryRepresentation.length - 1) * Long.SIZE));
		}

		public LinkedSetOrderedWithBits(int initSize, int nLevels) {
			this(initSize);
		}

		@Override
		protected void addElement(int e) {
			super.addElement(e);
			binaryRepresentation[e / Long.SIZE] |= Bit.ONE_LONG_BIT_TO_1[e % Long.SIZE];
			// binaryRepresentation[element >> 6] |= Bit.ONE_LONG_BIT_TO_1[element & ((1 << 6) - 1)];
		}

		@Override
		protected void removeElement(int e) {
			super.removeElement(e);
			binaryRepresentation[e / Long.SIZE] &= Bit.ONE_LONG_BIT_TO_0[e % Long.SIZE];
			// binaryRepresentation[element >> 6] &= Bit.ONE_LONG_BIT_TO_0[element & ((1 << 6) - 1)];
		}
	}

	public static final class LinkedSetOrderedWithBits2 extends LinkedSetOrderedWithBits {

		public final SetSparse set;

		public LinkedSetOrderedWithBits2(int initSize) {
			super(initSize);
			set = new SetSparse(binaryRepresentation.length, true);
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