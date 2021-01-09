/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package variables;

import java.util.Arrays;
import java.util.stream.IntStream;

import org.xcsp.common.Constants;
import org.xcsp.common.Range;
import org.xcsp.common.Utilities;

import propagation.Propagation;
import sets.LinkedSetOrdered.LinkedSetOrderedWithBits;
import utility.Kit;

/**
 * This class gives the description of the finite domain of a variable. <br>
 * A domain is attached to a variable and consists of a finite set of integer values. In order to simplify programming, most of the time indexes of values are
 * used instead of values. Indexes range from <code> 0 </code> to <code> initialSize -1 </code> where <code> initialSize </code> denote the number of elements
 * in the domain. For instance, if the domain contains the values <code> {1,4,5} </code>, their indexes are respectively <code> {0,1,2} </code>. The
 * correspondence between indexes of values and values is given by the methods <code> toIndex </code> and <code> toValue </code>.
 */
public abstract class DomainInteger extends LinkedSetOrderedWithBits implements Domain {

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof DomainInteger))
			return false;
		DomainInteger d = (DomainInteger) obj;
		if (this.size != d.size)
			return false;
		for (int a = first; a != -1; a = next(a))
			if (!d.present(a))
				return false;
		return true;
	}

	// @Override
	// public int hashCode() {
	// return 0; // i.hashCode();
	// }

	private Variable var;

	private Integer typeIdentifier;

	private Propagation propagation;

	private Boolean indexesMatchValues;

	@Override
	public final Variable var() {
		return var;
	}

	protected abstract int computeTypeIdentifier();

	@Override
	public final int typeIdentifier() {
		return typeIdentifier != null ? typeIdentifier : (typeIdentifier = computeTypeIdentifier());
	}

	@Override
	public final Propagation propagation() {
		return propagation;
	}

	@Override
	public final void setPropagation(Propagation propagation) {
		this.propagation = propagation;
	}

	@Override
	public final boolean indexesMatchValues() {
		return indexesMatchValues != null ? indexesMatchValues : (indexesMatchValues = IntStream.range(0, initSize()).noneMatch(a -> a != toVal(a)));
	}

	public DomainInteger(Variable var, int initSize) {
		super(initSize);
		this.var = var;
		Kit.control(0 < initSize && initSize <= Constants.MAX_SAFE_INT);
	}

	@Override
	public String toString() {
		return "dom(" + var().id() + ")";
	}

	/**
	 * This class gives the description of a domain composed of a list of integers included between two (integer) bounds.
	 */
	public final static class DomainRange extends DomainInteger {

		/** The minimal value of the domain. */
		public final int min;

		/** The maximal value of the domain. */
		public final int max;

		@Override
		protected int computeTypeIdentifier() {
			// TAG_RANGE used specially to avoid confusion with a domain only containing the two values min and max
			return Domain.typeIdentifierFor(min, max, TAG_RANGE);
		}

		public DomainRange(Variable var, int min, int max) {
			super(var, max - min + 1);
			this.min = min;
			this.max = max;
			Kit.control(Constants.MIN_SAFE_INT <= min && min <= max && max <= Constants.MAX_SAFE_INT, () -> "badly formed domain for variable " + var);
		}

		@Override
		public int toIdx(int v) {
			return v < min || v > max ? -1 : v - min;
		}

		@Override
		public int toVal(int a) {
			return (a + min) <= max ? a + min : -1;
		}

		@Override
		public Object allValues() {
			return new Range(min, max + 1);
		}
	}

	/**
	 * This class describes domains composed of a list of integers that are not necessarily contiguous. Be careful: the values are sorted.
	 */
	public static class DomainValues extends DomainInteger {

		public final int[] values;

		@Override
		protected int computeTypeIdentifier() {
			return Domain.typeIdentifierFor(this.values);
		}

		public DomainValues(Variable var, int... vals) {
			super(var, vals.length);
			this.values = IntStream.of(vals).sorted().distinct().toArray();
			Kit.control(Constants.MIN_SAFE_INT <= values[0] && values[values.length - 1] <= Constants.MAX_SAFE_INT);
		}

		@Override
		public int toIdx(int v) {
			return Arrays.binarySearch(values, v);
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
			// TAG_SYMBOLS used to avoid confusion with a "normal" domain containing exactly the same values as those associated with the
			// symbols
			return Domain.typeIdentifierFor(Utilities.collectInt(this.values, TAG_SYMBOLS));
		}

		public DomainSymbols(Variable var, int[] vals, String[] symbols) {
			super(var, vals);
			Kit.control(symbols != null && symbols.length > 0 && vals.length == symbols.length, () -> "badly formed set of symbols for variable " + var);
			// below we sort the array of symbols according to the way the array of values have been sorted (in the super-constructor)
			this.symbols = Arrays.stream(Kit.buildMapping(this.values, vals)).mapToObj(i -> symbols[i]).toArray(String[]::new);
		}

		@Override
		public String prettyValueOf(int a) {
			return symbols[a];
		}

		@Override
		public String stringListOfValues() {
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
