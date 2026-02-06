/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package variables;

import static utility.Kit.control;

import java.util.Arrays;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.stream.IntStream;

import org.xcsp.common.Constants;
import org.xcsp.common.Range;
import org.xcsp.common.Utilities;

import sets.SetDense;
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

	/**
	 * Computes and returns the type identifier of the domain
	 * 
	 * @return the type identifier of the domain
	 */
	protected abstract int computeTypeIdentifier();

	private Variable x;

	protected Integer typeIdentifier;

	protected Boolean indexesMatchValues;

	@Override
	public final Variable var() {
		return x;
	}

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
	}

	public static class DomainFiniteSpecial extends DomainFinite {

		public static final int UNINITIALIZED = -2;

		static int nTypes = 0;

		@Override
		public boolean equals(Object obj) {
			return false; // do not see how it could be equal to another object
		}

		@Override
		protected int computeTypeIdentifier() {
			throw new AssertionError("should not be called");
		}

		public void setNumberOfLevels(int nLevels) {
			super.setNumberOfLevels(nLevels);
			lbs = IntStream.generate(() -> UNINITIALIZED).limit(nLevels).toArray();
			ubs = IntStream.generate(() -> UNINITIALIZED).limit(nLevels).toArray();
			lbs[0] = initMinValue;
			ubs[0] = initMaxValue;
		}

		private final VariableInteger master;

		private final Domain masterDom;

		public final int initMinValue, initMaxValue, initSize, sliceLength, nSlices, nValuesLastSlice, nMissingValuesLastSlice;

		public int lb, ub;

		public int[] lbs;

		public int[] ubs;

		/**
		 * The minimal value of the current slice (relevant if the master domain is singleton)
		 */
		private int minSliceValue;

		/**
		 * The maximal value (included) of the current slice (relevant if the master domain is singleton)
		 */
		private int maxSliceValue;

		private int shiftDepth;

		public DomainFiniteSpecial(Variable x, VariableInteger master, int minValue, int maxValue, int sliceLength) {
			super(x, sliceLength);
			this.minSliceValue = minValue; // initially the first slice (but anyway, this is not relevant until the master is assigned
			this.maxSliceValue = minValue + sliceLength - 1;

			this.typeIdentifier = 1000 + nTypes++;
			this.indexesMatchValues = false;

			this.master = master;
			this.masterDom = master.dom;
			this.initMinValue = minValue;
			this.initMaxValue = maxValue;
			this.initSize = initMaxValue - initMinValue + 1;
			this.sliceLength = sliceLength;
			this.nSlices = master.dom.initSize();
			this.nValuesLastSlice = initSize % sliceLength == 0 ? sliceLength : initSize % sliceLength;
			this.nMissingValuesLastSlice = sliceLength - nValuesLastSlice;

			this.lb = initMinValue;
			this.ub = initMaxValue;
		}

		private void updateLB(int b) {
			if (b > lb) {
				int depth = var().problem.solver.depth();
				if (lbs[depth] == UNINITIALIZED)
					lbs[depth] = lb;
				lb = b;
			}
		}

		private void updateUB(int b) {
			if (b < ub) {
				int depth = var().problem.solver.depth();
				if (ubs[depth] == UNINITIALIZED)
					ubs[depth] = ub;
				ub = b;
			}
		}

		public boolean shift(int min) {
			control(masterDom.size() == 1);
			//control(nRemoved() == 0 || this.minSliceValue == min, nRemoved() + " ");
			var().problem.solver.stackVariable(var());

			this.shiftDepth = var().problem.solver.depth();
			this.minSliceValue = min;
			this.maxSliceValue = min + sliceLength - 1;

			this.lb = initMinValue;
			this.ub = initMaxValue;
			// System.out.println("hhhh " + minSliceValue + " " + maxSliceValue + " " + lb + " " + ub + " " + var());
			updateLB(minSliceValue);
			updateUB(maxSliceValue);
			// System.out.println("hhhh2 " + minSliceValue + " " + maxSliceValue + " " + lb + " " + ub + " " + var());

			boolean consistent = removeValuesLT(lb) && removeValuesGT(ub);
			control(consistent, "inconsistency not possible here");
			return handleReduction();
		}

		@Override
		public int initSize() {
			return initSize;
		}

		@Override
		public int size() {
			if (masterDom.size() == 1)
				return super.size();
			return ub - lb + 1; // masterDom.size() * sliceLength - (masterDom.last() == nSlices - 1 ? nMissingValuesLastSlice : 0);
		}

		public int practicalInitSize() {
			return sliceLength;
		}

		public int nRemoved() {
			if (masterDom.size() == 1)
				return sliceLength - size(); // do not call super.nRemoved()
			return initSize - (ub - lb + 1); // (nSlices - masterDom.size()) * sliceLength - (masterDom.last() < nSlices - 1 ? nMissingValuesLastSlice : 0);
		}

		@Override
		public final boolean contains(int a) {
			if (masterDom.size() == 1)
				return super.contains(a);
			return first() <= a && a <= last();
			// throw new AssertionError("should not be called");
		}

		public int first() {
			if (masterDom.size() == 1)
				return super.first();
			return lb - initMinValue; // masterDom.first() * sliceLength;
		}

		@Override
		public int next(int a) {
			if (masterDom.size() == 1)
				return super.next(a);
			throw new AssertionError("should not be called");
		}

		@Override
		public int last() {
			if (masterDom.size() == 1)
				return super.last();
			return ub - initMinValue; // masterDom.last() * sliceLength + (masterDom.last() == nSlices - 1 ? nValuesLastSlice : sliceLength);
		}

		@Override
		public int prev(int a) {
			if (masterDom.size() == 1)
				return super.prev(a);
			throw new AssertionError("should not be called");
		}

		public int get(int i) {
			if (masterDom.size() == 1)
				return super.get(i);
			throw new AssertionError("should not be called");
		}

		@Override
		public int lastRemoved() {
			if (masterDom.size() == 1)
				return super.lastRemoved();
			throw new AssertionError("should not be called");
		}

		@Override
		public int lastRemovedLevel() {
			if (masterDom.size() == 1) {
				if (nRemoved() == 0)
					return shiftDepth;
				return super.lastRemovedLevel();
			}
			throw new AssertionError("should not be called");
		}

		@Override
		public int removedLevelOf(int a) {
			if (masterDom.size() == 1)
				return super.removedLevelOf(a);
			throw new AssertionError("should not be called");
		}

		@Override
		public int prevRemoved(int a) {
			if (masterDom.size() == 1)
				return super.prevRemoved(a);
			throw new AssertionError("should not be called");
		}

		protected void removeElement(int a) {
			if (masterDom.size() == 1)
				super.removeElement(a);
			else
				throw new AssertionError("should not be called");
		}

		@Override
		public final void remove(int a, int level) {
			if (masterDom.size() == 1)
				super.remove(a, level);
			else
				throw new AssertionError("should not be called");
		}

		@Override
		public int reduceTo(int a, int level) {
			if (masterDom.size() == 1)
				return super.reduceTo(a, level);
			throw new AssertionError("should not be called");
		}

		protected void addElement(int a) {
			if (masterDom.size() == 1)
				super.addElement(a);
			else
				throw new AssertionError("should not be called");
		}

		protected void restoreLastDropped() {
			if (masterDom.size() == 1)
				super.restoreLastDropped();
			else
				throw new AssertionError("should not be called");
		}

		@Override
		public void restoreBefore(int level) {
			if (masterDom.size() == 1) {
				super.restoreBefore(level);
			} else {
				if (lbs[level] != UNINITIALIZED) {
					lb = lbs[level];
					lbs[level] = UNINITIALIZED;
				}
				if (ubs[level] != UNINITIALIZED) {
					ub = lbs[level];
					ubs[level] = UNINITIALIZED;
				}
			}
		}

		@Override
		public void setMark() {
			throw new AssertionError("should not be called");
		}

		@Override
		public int getMark() {
			throw new AssertionError("should not be called");
		}

		@Override
		public void restoreAtMark() {
			throw new AssertionError("should not be called");
		}

		@Override
		public void setMark(int level) {
			throw new AssertionError("should not be called");
		}

		@Override
		public void restoreAtMark(int level) {
			throw new AssertionError("should not be called");
		}

		public void execute(Consumer<Integer> consumer, boolean reverse) {
			throw new AssertionError("should not be called");
		}

		// public void execute(Consumer<Integer> consumer)

		public long[] binary() {
			throw new AssertionError("should not be called");
		}

		/**********************************************************************************************
		 * Methods from Domain
		 *********************************************************************************************/

		// public boolean initiallyRange(int nb)
		// public boolean initiallyRange(int a, int b)
		// public boolean initiallyRange(Range range)
		// public boolean initiallySubsetOf(int[] values)
		// public boolean initiallySubsetOf(Range range)

		public int toIdx(int v) {
			if (masterDom.size() == 1)
				return v < minSliceValue || v > maxSliceValue ? -1 : v - minSliceValue;
			return v < initMinValue || v > initMaxValue ? -1 : v - initMinValue;
		}

		@Override
		public int toVal(int a) {
			if (masterDom.size() == 1)
				return a + minSliceValue;
			return a + initMinValue;
		}

		// public boolean containsValue(int v)
		// public boolean containsOnly(int a)
		// public boolean containsOnlyValue(int v)

		// public int single()
		// public int any()
		// public int firstValue()
		// public int lastValue()
		// public int singleValue()
		// public int anyValue()

		// public int smallestInitialValue()
		// public int greatestInitialValue()

		// public int regretValue()
		// public int initDistance()
		// public int distance()

		public boolean is01() {
			return false;
		}

		public int commonValueWith(Domain dom) {
			if (masterDom.size() == 1)
				return super.commonValueWith(dom);
			throw new AssertionError("should not be called");
		}

		// public boolean overlapWith(Domain dom)

		public int commonValueWith(int[] values) {
			if (masterDom.size() == 1)
				return super.commonValueWith(values);
			throw new AssertionError("should not be called");
		}

		// public boolean overlapWith(int[] values)

		public boolean subsetOf(Domain dom) {
			if (masterDom.size() == 1)
				return super.subsetOf(dom);
			throw new AssertionError("should not be called");
		}

		// public boolean connex()
		// public boolean enclose(int minValueIncluded, int maxValueIncluded)

		public boolean enclose(int[] values) {
			if (masterDom.size() == 1)
				return super.enclose(values);
			throw new AssertionError("should not be called");
		}

		public boolean enclosedIn(int[] values) {
			if (masterDom.size() == 1)
				return super.enclosedIn(values);
			throw new AssertionError("should not be called");
		}

		public boolean withExactlyTheseValues(int[] values) {
			if (masterDom.size() == 1)
				return super.withExactlyTheseValues(values);
			throw new AssertionError("should not be called");
		}

		public int[] valuesChecking(Predicate<Integer> p) {
			if (masterDom.size() == 1)
				return super.valuesChecking(p);
			throw new AssertionError("should not be called");
		}

		public int indexOfValueClosestTo(int v) {
			throw new AssertionError("should not be called");
		}

		public int indexOfValueFarthestTo(int v) {
			throw new AssertionError("should not be called");
		}

		// public boolean handleReduction()

		public void removeAtConstructionTime(int a) {
			throw new AssertionError("should not be called");
		}

		public void removeAtConstructionTime(Predicate<Integer> p) {
			for (int a = first(); a != -1; a = next(a))
				if (p.test(a))
					throw new AssertionError("should not be called");
		}

		public void removeValueAtConstructionTime(int v) {
			throw new AssertionError("should not be called");
		}

		public void removeValuesAtConstructionTime(Predicate<Integer> p) {
			throw new AssertionError("should not be called");
		}

		public boolean afterElementaryCalls(int sizeBefore) {
			return size() == sizeBefore ? true : handleReduction();
		}

		public void removeElementary(int a) {
			if (masterDom.size() == 1)
				super.removeElementary(a);
			else
				throw new AssertionError("should not be called");
		}

		public boolean remove(int a) {
			if (masterDom.size() == 1)
				return super.remove(a);
			throw new AssertionError("should not be called");
		}

		public boolean removeIfPresent(int a) {
			if (masterDom.size() == 1)
				return super.removeIfPresent(a);
			throw new AssertionError("should not be called");
		}

		public boolean remove(boolean[] flags, int nRemovals) {
			if (masterDom.size() == 1)
				return super.remove(flags, nRemovals);
			throw new AssertionError("should not be called");
		}

		public boolean remove(SetDense idxs, boolean testPresence) {
			if (masterDom.size() == 1)
				return super.remove(idxs, testPresence);
			throw new AssertionError("should not be called");
		}

		public boolean remove(SetDense idxs) {
			if (masterDom.size() == 1)
				return super.remove(idxs);
			throw new AssertionError("should not be called");
		}

		public int reduceToElementary(int a) {
			if (masterDom.size() == 1)
				return super.reduceToElementary(a);
			throw new AssertionError("should not be called");
		}

		public boolean reduceTo(int a) {
			if (masterDom.size() == 1)
				return super.reduceTo(a);
			throw new AssertionError("should not be called");
		}

		public boolean reduceToValue(int v) {
			if (masterDom.size() == 1)
				return super.reduceToValue(v);
			throw new AssertionError("should not be called");
		}

		// default boolean fail() not overridden

		public boolean removeValue(int v) {
			if (masterDom.size() == 1)
				return super.removeValue(v);
			throw new AssertionError("should not be called");
		}

		public boolean removeValueIfPresent(int v) {
			if (masterDom.size() == 1)
				return super.removeValueIfPresent(v);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesLE(int limit) {
			if (lastValue() <= limit)
				return fail();
			if (firstValue() > limit)
				return true;
			
			if (masterDom.size() > 1)
				return true;
			
//			//var().problem.solver.stackVariable(var());
//			// we are sure to remove some values with no risk of inconsistency
//			if (masterDom.size() > 1) {
//				control(lb <= limit);
//				// first, we modify master dom
//				int k = (limit - initMinValue + 1) / sliceLength; // +1 because LE
//				boolean consistent = masterDom.removeValuesLT(k);
//				control(consistent, "inconsistency not possible here");
//				// second, we check if singleton
//				if (masterDom.size() == 1) {
//					int startValue = initMinValue + (masterDom.single() * sliceLength);
//					shift(startValue);
//					consistent = removeValuesGT(ub);
//					control(consistent, "inconsistency not possible here");
//					// the rest of the filtering is done below
//				} else { // we modify lb
//					int depth = var().problem.solver.depth();
//					if (lbs[depth] == UNINITIALIZED)
//						lbs[depth] = lb; // imit + 1;
//					lb = limit + 1;
//					control(masterDom.first() == (lb - initMinValue) / sliceLength && masterDom.last() == (ub - initMinValue) / sliceLength);
//					return handleReduction();
//				}
//			}
			
			control(masterDom.size() == 1);
			int sizeBefore = size();
			for (int a = first(); a != -1 && toVal(a) <= limit; a = next(a))
				removeElementary(a);
			return afterElementaryCalls(sizeBefore);
		}

		public boolean removeValuesGE(int limit) {
			if (firstValue() >= limit)
				return fail();
			if (lastValue() < limit)
				return true;
			control(masterDom.first() == (lb - initMinValue) / sliceLength && masterDom.last() == (ub - initMinValue) / sliceLength,
					"App1 " + masterDom.first() + " " + masterDom.last() + " " + lb + " " + ub + " " + limit + " " + var());
			
			if (masterDom.size() > 1)
				return true;
			
			//var().problem.solver.stackVariable(var());
			// we are sure to remove some values with no risk of inconsistency
//			if (masterDom.size() > 1) {
//
//				control(ub >= limit);
//				// first, we modify master dom
//				int k = (limit - initMinValue - 1) / sliceLength; // the first k indexes in masterDom are safe
//				boolean consistent = masterDom.removeValuesGT(k); // (limit - initMinValue) % sliceLength == 0 ? k : k + 1);
//				control(consistent, "inconsistency not possible here");
//				// second, we check if singleton
//				if (masterDom.size() == 1) {
//					int startValue = initMinValue + (masterDom.single() * sliceLength);
//					shift(startValue);
//					consistent = removeValuesLT(lb);
//					control(consistent, "inconsistency not possible here");
//					// the rest of the filtering is done below
//				} else { // we modify lb
//					int depth = var().problem.solver.depth();
//					if (ubs[depth] == UNINITIALIZED)
//						ubs[depth] = ub; // limit - 1;
//					ub = limit - 1;
//					control(masterDom.first() == (lb - initMinValue) / sliceLength && masterDom.last() == (ub - initMinValue) / sliceLength,
//							"App2 " + masterDom.first() + " " + masterDom.last() + " " + limit);
//					return handleReduction();
//				}
//			}
			
			control(masterDom.size() == 1);
			int sizeBefore = size();
			for (int a = last(); a != -1 && toVal(a) >= limit; a = prev(a))
				removeElementary(a);
			return afterElementaryCalls(sizeBefore);
		}

		// default boolean removeValuesLT(int limit)
		// default boolean removeValuesGT(int limit)
		// default boolean removeValuesLT(long limit)
		// default boolean removeValuesGT(long limit)

		// boolean removeValues(TypeOperatorRel type, long limit, int coeff)

		public boolean removeValuesModIn(Domain dom, int coeff) {
			if (masterDom.size() == 1)
				return super.removeValuesModIn(dom, coeff);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesAtDistanceGT(int k, Domain dom) {
			if (masterDom.size() == 1)
				return super.removeValuesAtDistanceGT(k, dom);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesNumeratorsGT(int k, int denominator) {
			if (masterDom.size() == 1)
				return super.removeValuesNumeratorsGT(k, denominator);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesDenominatorsGT(int k, int numerator) {
			if (masterDom.size() == 1)
				return super.removeValuesDenominatorsGT(k, numerator);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesNumeratorsLT(int k, int denominator) {
			if (masterDom.size() == 1)
				return super.removeValuesNumeratorsLT(k, denominator);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesDenominatorsLT(int k, int numerator) {
			if (masterDom.size() == 1)
				return super.removeValuesDenominatorsLT(k, numerator);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesIn(Domain dom) {
			if (masterDom.size() == 1)
				return super.removeValuesIn(dom);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesNotIn(Domain dom) {
			if (masterDom.size() == 1)
				return super.removeValuesNotIn(dom);
			throw new AssertionError("should not be called");
		}

		public boolean removeSurplusValuesWrt(Domain dom) {
			if (masterDom.size() == 1)
				return super.removeSurplusValuesWrt(dom);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesIn(Set<Integer> set) {
			if (masterDom.size() == 1)
				return super.removeValuesIn(set);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesNotIn(Set<Integer> set) {
			if (masterDom.size() == 1)
				return super.removeValuesNotIn(set);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesIn(int[] set) {
			if (masterDom.size() == 1)
				return super.removeValuesIn(set);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesNotIn(int[] set) {
			if (masterDom.size() == 1)
				return super.removeValuesNotIn(set);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesIn(SetDense set) {
			if (masterDom.size() == 1)
				return super.removeValuesIn(set);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesInRange(int start, int stop) {
			if (masterDom.size() == 1)
				return super.removeValuesInRange(start, stop);
			throw new AssertionError("should not be called");
		}

		public boolean removeIndexesChecking(Predicate<Integer> p) {
			if (masterDom.size() == 1)
				return super.removeIndexesChecking(p);
			throw new AssertionError("should not be called");
		}

		public boolean removeValuesChecking(Predicate<Integer> p) {
			if (masterDom.size() == 1)
				return super.removeValuesChecking(p);
			throw new AssertionError("should not be called");
		}

		/******/

		@Override
		public Object allValues() {
			if (masterDom.size() == 1)
				return new Range(minSliceValue, maxSliceValue + 1);
			return new Range(initMinValue, initMaxValue + 1);

		}

		public boolean controlStructures() {
			if (masterDom.size() == 1)
				return super.controlStructures();
			return true; // TODO checking something?
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
