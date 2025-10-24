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

import static utility.Kit.control;

import java.util.Arrays;
import java.util.stream.IntStream;

import org.xcsp.common.Constants;
import org.xcsp.common.Range;
import org.xcsp.common.Utilities;

import sets.SetLinkedFinite.SetLinkedFiniteWithBits;
import utility.Kit;
import variables.Variable.VariableInteger;

/**
 * A finite domain for a variable (from a constraint network), composed of a finite set of integers. Such a domain is defined from a range or an array; see the
 * two intern subclasses.
 * 
 * @author Christophe Lecoutre
 */
public abstract class DomainFinite extends SetLinkedFiniteWithBits implements Domain {

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof DomainFinite))
			return false;
		DomainFinite d = (DomainFinite) obj;
		if (this.size != d.size)
			return false;
		for (int a = first; a != -1; a = next(a))
			if (!d.contains(a))
				return false;
		return true;
	}

	private Variable x;

	protected Integer typeIdentifier;

	protected Boolean indexesMatchValues;

	@Override
	public final Variable var() {
		return x;
	}

	/**
	 * Computes and returns the type identifier of the domain
	 * 
	 * @return the type identifier of the domain
	 */
	protected abstract int computeTypeIdentifier();

	@Override
	public final int typeIdentifier() {
		return typeIdentifier != null ? typeIdentifier : (typeIdentifier = computeTypeIdentifier());
	}

	@Override
	public final boolean indexesMatchValues() {
		return indexesMatchValues != null ? indexesMatchValues : (indexesMatchValues = IntStream.range(0, initSize()).noneMatch(a -> a != toVal(a)));
	}

	/**
	 * Builds a finite domain of the specified initial size for the specified variable
	 * 
	 * @param x
	 *            the variable to which the domain is associated
	 * @param initSize
	 *            the initial size of the domain
	 */
	public DomainFinite(Variable x, int initSize) {
		super(initSize);
		this.x = x;
		control(0 < initSize && initSize <= Constants.MAX_SAFE_INT);
	}

	@Override
	public String toString() {
		return "dom(" + var() + ")";
	}

	/**********************************************************************************************
	 * DomainRange
	 *********************************************************************************************/

	/**
	 * This class gives the description of a domain composed of a list of integers included between two (integer) bounds.
	 */
	public abstract static class DomainRange extends DomainFinite {

		public static DomainRange buildDomainRange(Variable x, int min, int max) {
			return min == 0 ? new DomainRangeM(x, min, max) : new DomainRangeG(x, min, max);
		}

		/**
		 * The minimal value of the domain
		 */
		protected int min;

		/**
		 * The maximal value of the domain (included)
		 */
		protected int max;

		@Override
		protected int computeTypeIdentifier() {
			return Domain.typeIdentifierForRange(min, max);
		}

		public DomainRange(Variable x, int min, int max) {
			super(x, max - min + 1);
			this.min = min;
			this.max = max;
			control(Constants.MIN_SAFE_INT <= min && min <= max && max <= Constants.MAX_SAFE_INT, () -> "badly formed domain for variable " + x);
		}

		@Override
		public Object allValues() {
			return new Range(min, max + 1);
		}
	}

	/**
	 * This class gives the description of a general range domain.
	 */
	public static class DomainRangeG extends DomainRange {

		public DomainRangeG(Variable x, int min, int max) {
			super(x, min, max);
		}

		@Override
		public int toIdx(int v) {
			return v < min || v > max ? -1 : v - min;
		}

		@Override
		public int toVal(int a) {
			// assert a + min <= max;
			return a + min;
		}

	}

	public static class DomainRangeGSpecial extends DomainRangeG {

		private final VariableInteger master;

		public int initMinValue, initMaxValue, initSize, sliceLength;

		@Override
		public boolean equals(Object obj) {
			return false;
		}

		static int nTypes = 0;

		public DomainRangeGSpecial(Variable x, VariableInteger master, int minValue, int maxValue, int sliceLength) {
			super(x, minValue, minValue + sliceLength - 1); // initially the first slice (but anyway, this is not relevant until the master is assigned)
			this.typeIdentifier = 1000 + nTypes++;
			this.indexesMatchValues = false;
			this.master = master;
			this.initMinValue = minValue;
			this.initMaxValue = maxValue;
			this.initSize = initMaxValue - initMinValue + 1;
			this.sliceLength = sliceLength;
			// System.out.println("qqqqqqqqqq" + initMinValue + " " + initMaxValue + " " +initSize);
		}

		public void shift(int min, int max) {
			control(nRemoved() == 0);
			control(max - min + 1 == sliceLength);
			this.min = min;
			this.max = max;
		}

		@Override
		public int initSize() {
			if (!master.assigned())
				return initSize;
			return super.initSize();
		}

		public int toIdx(int v) {
			if (!master.assigned())
				return v < initMinValue || v > initMaxValue ? -1 : v - initMinValue;
			return v < min || v > max ? -1 : v - min;
		}

		@Override
		public int toVal(int a) {
			if (!master.assigned())
				return a + initMinValue;
			// assert a + min <= max;
			return a + min;
		}

		public int first() {
			if (!master.assigned())
				return 0;
			return first;
		}

		@Override
		public int last() {
			if (!master.assigned())
				return initSize - 1;
			return last;
		}

		protected void removeElement(int a) {
			if (!master.assigned())
				throw new UnknownError("pb");
			super.removeElement(a);
		}

		@Override
		public void restoreBefore(int level) {
			// if (!leadingVariable.waked())
			// this.
			// else
			super.restoreBefore(level);

		}

		// protected void addElement(int a) {
		// if (!leadingVariable.waked())
		// throw new UnknownError("pb");
		// super.addElement(a);
		// }

		public void removeAtConstructionTime(int a) {
			throw new UnknownError("pb");
		}

		@Override
		public Object allValues() {
			if (!master.assigned())
				return new Range(initMinValue, initMaxValue + 1);
			return new Range(min, max + 1);
		}
	}

	/**
	 * This class gives the description of a range domain where index and values match, i.e., a range starting at 0.
	 */
	public final static class DomainRangeM extends DomainRange {

		public DomainRangeM(Variable x, int min, int max) {
			super(x, min, max);
			control(min == 0 && 0 <= max && max <= Constants.MAX_SAFE_INT, () -> "badly formed domain for variable " + x);
		}

		@Override
		public int firstValue() {
			return first;
		}

		@Override
		public int lastValue() {
			return last;
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
			return v < 0 || v > max ? -1 : v;
		}

		@Override
		public int toVal(int a) {
			// assert 0 <= a && a <= max;
			return a;
		}

		@Override
		public boolean containsValue(int v) {
			return (0 <= v && v <= max) && contains(v);
		}

		@Override
		public boolean containsOnlyValue(int v) {
			return size == 1 && v == first;
		}
	}

	/**********************************************************************************************
	 * DomainValues and DomainSymbols
	 *********************************************************************************************/

	/**
	 * This class describes domains composed of a list of integers that are not necessarily contiguous. Be careful: the values are sorted.
	 */
	public static class DomainValues extends DomainFinite {

		private static final int DIRECT_INDEXING_LIMIT = 1000; // TODO hard coding

		/**
		 * The values of the domain
		 */
		public final int[] values;

		/**
		 * The indexes of values (possibly null)
		 */
		public final int[] indexes;

		private int firstValue, lastValue;

		@Override
		protected int computeTypeIdentifier() {
			return Domain.typeIdentifierFor(values);
		}

		public DomainValues(Variable x, int... values) {
			super(x, values.length);
			assert Kit.isStrictlyIncreasing(values);
			assert this instanceof DomainSymbols || IntStream.range(0, values.length - 1).anyMatch(i -> values[i + 1] != values[i] + 1);
			control(Constants.MIN_SAFE_INT <= values[0] && values[values.length - 1] <= Constants.MAX_SAFE_INT);
			this.values = values;
			this.firstValue = values[0];
			this.lastValue = values[values.length - 1];
			if (lastValue - firstValue < DIRECT_INDEXING_LIMIT) {
				this.indexes = Kit.repeat(-1, lastValue - firstValue + 1);
				for (int i = 0; i < values.length; i++)
					indexes[values[i] - firstValue] = i;
			} else
				this.indexes = null;
		}

		@Override
		public int toIdx(int v) {
			if (indexes != null)
				return v < firstValue || v > lastValue ? -1 : indexes[v - firstValue];
			return Arrays.binarySearch(values, v); // TODO should we prefer using a map ? it seems so, but to be tested.
		}

		@Override
		public final int toVal(int a) {
			return values[a];
		}

		@Override
		public Object allValues() {
			return values;
		}
	}

	/**
	 * This class describes domains composed of a list of symbols, where each such symbol is associated with a value (just introduced to handle symbols in the
	 * solver).
	 */
	public final static class DomainSymbols extends DomainValues {

		public final String[] symbols;

		@Override
		protected int computeTypeIdentifier() {
			return Domain.typeIdentifierForSymbols(values);
		}

		public DomainSymbols(Variable x, int[] vals, String[] symbols) {
			super(x, vals);
			control(symbols != null && symbols.length > 0 && vals.length == symbols.length, () -> "badly formed set of symbols for variable " + x);
			// below we sort the array of symbols according to the way the array of values have been sorted (in the
			// super-constructor)
			int[] mapping = IntStream.range(0, values.length).map(i -> Utilities.indexOf(values[i], vals)).toArray();
			this.symbols = IntStream.of(mapping).mapToObj(i -> symbols[i]).toArray(String[]::new);
		}

		@Override
		public String prettyValueOf(int a) {
			return symbols[a];
		}

		@Override
		public String stringOfCurrentValues() {
			StringBuilder sb = new StringBuilder();
			for (int a = first(); a != -1; a = next(a))
				sb.append(a != first() ? ' ' : "").append(symbols[a]);
			return sb.toString();
		}

		public int toIdx(String v) {
			return Utilities.indexOf(v, symbols); // TODO using a map instead ?
		}
	}

}
