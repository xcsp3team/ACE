/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package variables;

import java.util.stream.IntStream;

import sets.SetLinkedBinary;
import utility.Kit;

/**
 * A binary domain for a variable (entity of a constraint network).
 * 
 * @author Christophe Lecoutre
 */
public abstract class DomainBinary extends SetLinkedBinary implements Domain {

	public static DomainBinary buildDomainBinary(Variable x, int firstValue, int secondValue) {
		return firstValue == 0 && secondValue == 1 ? new DomainBinaryS(x, firstValue, secondValue) : new DomainBinaryG(x, firstValue, secondValue);
	}

	protected Variable x;

	protected Integer typeIdentifier;

	protected Boolean indexesMatchValues;

	protected int firstValue, secondValue; // typically, 0 and 1

	@Override
	public final Variable var() {
		return x;
	}

	@Override
	public final int typeIdentifier() {
		return typeIdentifier != null ? typeIdentifier : (typeIdentifier = Domain.typeIdentifierFor(firstValue, secondValue));
	}

	@Override
	public final boolean indexesMatchValues() {
		return indexesMatchValues != null ? indexesMatchValues : (indexesMatchValues = IntStream.range(0, initSize()).noneMatch(a -> a != toVal(a)));
	}

	public DomainBinary(Variable x, int firstValue, int secondValue) {
		this.x = x;
		this.firstValue = firstValue;
		this.secondValue = secondValue;
	}

	@Override
	public Object allValues() {
		return new int[] { firstValue, secondValue };
	}

	@Override
	public String toString() {
		return "dom(" + var() + ")";
	}

	/**********************************************************************************************
	 * Subclasses G for General and S for Specific (when indexes match values)
	 *********************************************************************************************/

	public static final class DomainBinaryG extends DomainBinary {

		/**
		 * Builds a binary domain for the specified variable from the specified values
		 * 
		 * @param x
		 *            the variable to which the domain is associated
		 * @param firstValue
		 *            the first value of the domain
		 * @param secondValue
		 *            the second value of the domain
		 */
		public DomainBinaryG(Variable x, int firstValue, int secondValue) {
			super(x, firstValue, secondValue);
		}

		@Override
		public int toIdx(int v) {
			return v == firstValue ? 0 : v == secondValue ? 1 : -1;
		}

		@Override
		public int toVal(int a) {
			// assert a == 0 || a == 1;
			return a == 0 ? firstValue : secondValue;
		}

	}

	public static final class DomainBinaryS extends DomainBinary {

		public static final int[] values = { 0, 1 };

		@Override
		public Object allValues() {
			return values;
		}

		/**
		 * Builds a binary domain for the specified variable from the specified values
		 * 
		 * @param x
		 *            the variable to which the domain is associated
		 * @param firstValue
		 *            the first value of the domain
		 * @param secondValue
		 *            the second value of the domain
		 */
		public DomainBinaryS(Variable x, int firstValue, int secondValue) {
			super(x, firstValue, secondValue);
			Kit.control(firstValue == 0 && secondValue == 1);
		}

		@Override
		public int first() {
			if (size == 0)
				return -1;
			return lastRemoved != 0 ? 0 : 1;
		}

		@Override
		public int last() {
			if (size == 0)
				return -1;
			return lastRemoved != 1 ? 1 : 0;
		}

		@Override
		public int firstValue() {
			if (size == 0)
				return -1;
			return lastRemoved != 0 ? 0 : 1;
		}

		@Override
		public int lastValue() {
			if (size == 0)
				return -1;
			return lastRemoved != 1 ? 1 : 0;
		}

		@Override
		public int singleValue() {
			return single();
		}

		@Override
		public int anyValue() {
			return any();
		}

		@Override
		public int toIdx(int v) {
			return v == 0 || v == 1 ? v : -1;
		}

		@Override
		public int toVal(int a) {
			// assert a == 0 || a == 1;
			return a;
		}

		@Override
		public boolean containsValue(int v) {
			return (v == 0 || v == 1) && contains(v);
		}

		@Override
		public boolean containsOnlyValue(int v) {
			return size() == 1 && v == first();
		}

	}

}