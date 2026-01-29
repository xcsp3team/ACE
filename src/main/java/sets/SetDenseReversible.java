/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package sets;

import static utility.Kit.control;

import java.util.Arrays;
import java.util.stream.IntStream;

/**
 * A reversible dense set is a dense set that can be handled at different levels.
 * 
 * @author Christophe Lecoutre
 */
public class SetDenseReversible extends SetDense {
	/**
	 * limits[i] is the limit of the dense set at level i
	 */
	public final int[] limits;

	@Override
	public void clear() {
		super.clear();
		Arrays.fill(limits, UNINITIALIZED);
	}

	@Override
	public void fill() {
		super.fill();
		Arrays.fill(limits, UNINITIALIZED);
	}

	/**
	 * Builds a reversible dense set from the values in the specified array, and with the specified number of possible levels. These values are those that can
	 * be contained at any time in the set. Most of the time, these values are exactly the indexes 0, 1, 2, ... and the dense set is then said to be simple.
	 * Initially, the set is full or empty depending on the value of the specified boolean.
	 * 
	 * @param dense
	 * @param nLevels
	 *            the number of different levels at which the set can be handled
	 * @param initiallyFull
	 *            if true, the set is initially full, empty otherwise
	 */
	public SetDenseReversible(int[] dense, int nLevels, boolean initiallyFull) {
		super(dense, initiallyFull);
		control(nLevels > 0);
		limits = IntStream.generate(() -> UNINITIALIZED).limit(nLevels).toArray();
	}

	/**
	 * Builds a reversible dense set with the specified capacity and the specified number of possible levels. The dense set is simple, meaning that it is aimed
	 * at containing indexes 0, 1, 2, ... Initially, the set is full or empty depending on the value of the specified boolean.
	 * 
	 * @param capacity
	 *            the capacity of the dense set
	 * @param nLevels
	 *            the number of different levels at which the set can be handled
	 * @param initiallyFull
	 *            if true, the set is initially full, empty otherwise
	 */
	public SetDenseReversible(int capacity, int nLevels, boolean initiallyFull) {
		this(IntStream.range(0, capacity).toArray(), nLevels, initiallyFull);
	}

	/**
	 * Builds a reversible dense set with the specified capacity and the specified number of possible levels. The dense set is simple, meaning that it is aimed
	 * at containing indexes 0, 1, 2, ... Initially, the set is full.
	 * 
	 * @param capacity
	 *            the capacity of the dense set
	 * @param nLevels
	 *            the number of different levels at which the set can be handled
	 */
	public SetDenseReversible(int capacity, int nLevels) {
		this(capacity, nLevels, true);
	}

	/**
	 * Records the current limit at the specified level, which can be restored later
	 * 
	 * @param level
	 *            an integer
	 */
	public final void storeLimitAtLevel(int level) {
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
	}

	/**
	 * Restores the limit that was recorded earlier at the specified level
	 * 
	 * @param level
	 *            an integer
	 */
	public final void restoreLimitAtLevel(int level) {
		if (limits[level] != UNINITIALIZED) {
			limit = limits[level];
			limits[level] = UNINITIALIZED;
		}
	}

	/**
	 * Removes the element at the specified position. Technically, this element is swapped with the last one, before decrementing the limit of the set. If this
	 * is the first element removed at the specified level, the current limit for this level is recorded.
	 * 
	 * @param i
	 *            the position of the element to be removed
	 * @param level
	 *            the level at which this operation occurs
	 */
	public void removeAtPosition(int i, int level) {
		storeLimitAtLevel(level);
		removeAtPosition(i);
	}
}
