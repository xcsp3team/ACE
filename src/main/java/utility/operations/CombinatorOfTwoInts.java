/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package utility.operations;

import utility.Kit;

/*
 * This class allows to represent two integer values inside a single int or long value. 
 */
public final class CombinatorOfTwoInts {
	private final int maxLeftValue, maxRightValue;
	private final int offset; // used for managing pairs of values as a unique int

	public long maxPossibleCombinedValue() {
		return maxLeftValue * offset + maxRightValue;
	}

	public int leftValueIn(int combinedValue) {
		assert 0 <= combinedValue && combinedValue <= maxPossibleCombinedValue();
		return combinedValue / offset;
	}

	public int rightValueIn(int combinedValue) {
		assert 0 <= combinedValue && combinedValue <= maxPossibleCombinedValue();
		return combinedValue % offset;
	}

	public int leftValueIn(long combinedValue) {
		assert 0 <= combinedValue && combinedValue <= maxPossibleCombinedValue();
		return (int) combinedValue / offset;
	}

	public int rightValueIn(long combinedValue) {
		assert 0 <= combinedValue && combinedValue <= maxPossibleCombinedValue();
		return (int) combinedValue % offset;
	}

	public int combinedIntValueFor(int leftValue, int rightValue) {
		assert 0 <= leftValue && leftValue <= maxLeftValue && 0 <= rightValue && rightValue <= maxRightValue && maxPossibleCombinedValue() <= Integer.MAX_VALUE;
		return leftValue * offset + rightValue;
	}

	public long combinedLongValueFor(int leftValue, int rightValue) {
		assert 0 <= leftValue && leftValue <= maxLeftValue && 0 <= rightValue && rightValue <= maxRightValue;
		return leftValue * offset + rightValue;
	}

	public long combinedMinMaxLongValueFor(int leftValue, int rightValue) {
		assert 0 <= leftValue && leftValue <= maxLeftValue && 0 <= rightValue && rightValue <= maxRightValue;
		return (maxLeftValue - leftValue) * offset + rightValue;
	}

	public long combinedMaxMinLongValueFor(int leftValue, int rightValue) {
		assert 0 <= leftValue && leftValue <= maxLeftValue && 0 <= rightValue && rightValue <= maxRightValue;
		return leftValue * offset + (maxRightValue - rightValue);
	}

	public CombinatorOfTwoInts(int maxLeftValue, int maxRightValue) {
		this.maxLeftValue = maxLeftValue;
		this.maxRightValue = maxRightValue;
		this.offset = maxRightValue + 1;
		Kit.control(0 < maxLeftValue && 0 < maxRightValue && (double) maxLeftValue * offset + maxRightValue <= Long.MAX_VALUE);
	}

	public CombinatorOfTwoInts(int maxRightValue) {
		this(Integer.MAX_VALUE - 1, maxRightValue);
	}

	public CombinatorOfTwoInts() {
		this(Integer.MAX_VALUE - 1, Integer.MAX_VALUE - 1);
	}
}
