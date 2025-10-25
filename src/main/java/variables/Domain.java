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

import static org.xcsp.common.Types.TypeOperatorRel.GE;
import static org.xcsp.common.Types.TypeOperatorRel.GT;
import static org.xcsp.common.Types.TypeOperatorRel.LE;
import static org.xcsp.common.Types.TypeOperatorRel.LT;
import static utility.Kit.control;

import java.math.BigInteger;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Range;
import org.xcsp.common.Types.TypeOperatorRel;
import org.xcsp.common.Utilities;

import interfaces.Observers.ObserverOnRemovals;
import problem.Problem;
import sets.SetDense;
import sets.SetLinked;
import solver.Solver;
import utility.Kit;

/**
 * A domain for a variable (entity of a constraint network) is composed of a set of integer values. The domain is initially full, but typically reduced when
 * logically reasoning (with constraints). When handling a domain, to simplify programming, one usually iterates over the indexes of the values; if the domains
 * contains d values, the indexes then range from 0 to d-1. For instance, if the domain is the set of values <code> {1,4,5} </code>, their indexes are
 * respectively <code> {0,1,2} </code>. The correspondence between indexes of values and values is given by the methods <code> toIdx </code> and
 * <code> toVal </code>.
 *
 * @author Christophe Lecoutre
 */
public interface Domain extends SetLinked {

	/**********************************************************************************************
	 * Static Members
	 *********************************************************************************************/

	static final DecimalFormat df2 = new DecimalFormat("00");
	static final DecimalFormat df3 = new DecimalFormat("000");
	static final DecimalFormat df4 = new DecimalFormat("0000");

	/**
	 * The cache used for storing type identifiers.
	 */
	static final List<int[]> types = new ArrayList<>();

	/**
	 * Returns a type identifier for the specified array of values (integers), while using a cache
	 * 
	 * @param values
	 *            an array of values (integers)
	 * @return a type identifier
	 */
	static int typeIdentifierFor(int... values) {

		int j = IntStream.range(0, types.size()).filter(i -> Arrays.equals(values, types.get(i))).findFirst().orElse(-1);
		if (j != -1)
			return j;
		types.add(values);
		return types.size() - 1;
	}

	/**
	 * Returns a type identifier for the specified range of values (integers), while using a cache
	 * 
	 * @param min
	 *            the minimal value of the range
	 * @param max
	 *            the maximal value of the range (included)
	 * @return a type identifier
	 */
	static int typeIdentifierForRange(int min, int max) {
		// adding a third value, Integer.MAX_VALUE, which is not an authorized domain value since there is a safety
		// margin, to specify a range (avoiding confusion with a domain only containing min and max)
		return typeIdentifierFor(min, max, Integer.MAX_VALUE);
	}

	/**
	 * Returns a type identifier for the specified array of values (corresponding to symbols), while using a cache
	 * 
	 * @param values
	 *            values (corresponding to symbols)
	 * @return a type identifier
	 */
	static int typeIdentifierForSymbols(int... values) {
		// adding a third value, Integer.MAX_VALUE -1, which is not an authorized domain value since there is a safety
		// margin, to specify a domain of symbols (avoiding confusion with a domain containing the specified integers)
		return typeIdentifierFor(Utilities.collectInt(values, Integer.MAX_VALUE - 1));
	}

	/**
	 * Returns true if the two arrays of domains are similar when considering type identifiers in sequence
	 * 
	 * @param doms1
	 *            a first array of domain
	 * @param doms2
	 *            a second array of domains
	 * @return true if the two arrays of domains have similar sequential type identifiers
	 */
	static boolean similarTypes(Domain[] doms1, Domain[] doms2) {
		return doms1.length == doms2.length && IntStream.range(0, doms1.length).allMatch(i -> doms1[i].typeIdentifier() == doms2[i].typeIdentifier());
	}

	/**
	 * Records a mark in the domain of each variable of the specified array
	 * 
	 * @param vars
	 *            an array of variables
	 */
	static void setMarks(Variable[] vars) {
		for (Variable x : vars)
			x.dom.setMark();
	}

	/**
	 * Restores the domain of each variable of the specified array with the previously recorded marks
	 * 
	 * @param vars
	 *            an array of variables
	 */
	static void restoreAtMarks(Variable[] vars) {
		for (Variable x : vars)
			x.dom.restoreAtMark();
	}

	/**
	 * Returns the number of valid tuples in the Cartesian product of the specified domains
	 * 
	 * @param doms
	 *            an array of domains
	 * @param initial
	 *            true if the initial size of the domains must be considered, otherwise the current size
	 * @return the number of valid tuples
	 */
	static BigInteger nValidTuples(Domain[] doms, boolean initial) {
		BigInteger prod = BigInteger.ONE;
		for (Domain dom : doms)
			prod = prod.multiply(BigInteger.valueOf(initial ? dom.initSize() : dom.size()));
		return prod;
	}

	/**
	 * Returns either the number of valid tuples or Long.MAX_VALUE if the exact number is greater than Long.MAX_VALUE
	 * 
	 * @param doms
	 *            an array of domains
	 * @param discardedPosition
	 *            the position of a domain that must be discarded
	 * @return the number of valid tuples or Long.MAX_VALUE
	 */
	static long nValidTuplesBounded(Domain[] doms, int discardedPosition) {
		assert Stream.of(doms).noneMatch(dom -> dom.size() == 0);
		long l = 1;
		for (int i = 0; i < doms.length; i++) {
			if (i == discardedPosition)
				continue;
			int size = doms[i].size(); // generalizing with a parameter (initial)?
			long ll = l * size;
			if (ll / size != l)
				return Long.MAX_VALUE; // because overflow
			l = ll;
		}
		return l;
	}

	/**
	 * Returns either the number of valid tuples or Long.MAX_VALUE if the exact number is greater than Long.MAX_VALUE
	 * 
	 * @param doms
	 *            an array of domains
	 * @return the number of valid tuples or Long.MAX_VALUE
	 */
	static long nValidTuplesBounded(Domain... doms) {
		return nValidTuplesBounded(doms, -1);
	}

	/**
	 * Returns the index of the greatest value of the specified domain which is less than the specified value. When true, the specified Boolean requires
	 * strictness. If no such value exists, -1 is returned.
	 * 
	 * @param dom
	 *            a domain
	 * @param v
	 *            a value
	 * @param strict
	 *            indicates if '<' must be considered instead of '<=' when looking for the greatest value
	 * @return the index of the greatest value of the specified domain which is less than the specified value, or -1
	 */
	static int greatestIndexOfValueLessThan(Domain dom, int v, boolean strict) {
		int d = dom.initSize();
		return IntStream.range(0, d).map(a -> d - 1 - a).filter(a -> dom.toVal(a) <= v + (strict ? -1 : 0)).findFirst().orElse(-1);
	}

	/**
	 * Returns the index of the smallest value of the specified domain which is greater than the specified value. When true, the specified Boolean requires
	 * strictness. If no such value exists, Integer.MAX_VALUE is returned.
	 * 
	 * @param dom
	 *            a domain
	 * @param v
	 *            a value
	 * @param strict
	 *            indicates if '>' must be considered instead of '>=' when looking for the smallest value
	 * @return the index of the greatest value of the specified domain which is less than the specified value, or -1
	 */
	static int smallestIndexOfValueGreaterThan(Domain dom, int v, boolean strict) {
		int d = dom.initSize();
		return IntStream.range(0, d).filter(a -> dom.toVal(a) >= v + (strict ? 1 : 0)).findFirst().orElse(Integer.MAX_VALUE);
	}

	/**********************************************************************************************
	 * Class Members
	 *********************************************************************************************/

	/**
	 * @param range
	 *            a number corresponding to the range 0 to itself -1
	 * @return true if the initial domain exactly corresponds to the specified range
	 */
	default boolean initiallyRange(int nb) {
		return initSize() == nb && toVal(0) == 0 && toVal(nb - 1) == nb - 1;
	}

	/**
	 * @param a
	 *            the start value (included) of the range
	 * @param b
	 *            the stop value (excluded) of the range
	 * @return true if the initial domain exactly corresponds to the specified range
	 */
	default boolean initiallyRange(int a, int b) {
		return initSize() == (b - a) && toVal(0) == a && toVal(b - a - 1) == b - 1;
	}

	/**
	 * @param range
	 *            a range of values
	 * @return true if the initial domain exactly corresponds to the specified range
	 */
	default boolean initiallyRange(Range range) {
		control(range.step == 1);
		return initSize() == range.length() && IntStream.range(0, initSize()).allMatch(a -> toVal(a) == range.start + a);
	}

	/**
	 * @param values
	 *            an array of values
	 * @return true if the initial domain is a subset of the specified set of values
	 */
	default boolean initiallySubsetOf(int[] values) {
		return initSize() <= values.length && IntStream.range(0, initSize()).allMatch(a -> Kit.isPresent(toVal(a), values));
	}

	/**
	 * @param range
	 *            a range of values
	 * @return true if the initial domain is a subset of the specified range
	 */
	default boolean initiallySubsetOf(Range range) {
		control(range.step == 1);
		return initSize() <= range.length() && IntStream.range(0, initSize()).allMatch(a -> range.start <= toVal(a) && toVal(a) < range.stop);
	}

	/**
	 * @return the variable to which the domain is attached
	 */
	Variable var();

	/**
	 * Returns the type identifier of the domain. Similar domains share the same type identifier.
	 * 
	 * @return the type identifier of the domain
	 */
	int typeIdentifier();

	/**
	 * @return the name of the type of the domain
	 */
	default String typeName() {
		return "D" + typeIdentifier();
	}

	/**
	 * Indicates if value indexes and values match, i.e. if for every index a, we have toVal(a) = a, and for every value v, we have toIdx(v)=v.
	 * 
	 * @return {@code true} iff indexes (of values) and values match
	 */
	boolean indexesMatchValues();

	/**
	 * Returns the index of the specified value, or a negative integer if the specified value does not belong to the initial domain. No assumption is made about
	 * the fact that the specified value belongs or not to the current domain.
	 * 
	 * @param v
	 *            a value
	 * @return the index of the specified value
	 */
	int toIdx(int v);

	/**
	 * Returns the value at the specified index. The index is assumed to be a valid one, i.e., an integer between 0 and d-1 where d is the initial size of the
	 * domain.
	 * 
	 * @param a
	 *            a value index
	 * @return the value at the specified index
	 */
	int toVal(int a);

	/**
	 * @param v
	 *            a value
	 * @return the index of the specified value if it belongs to the current domain, -1 otherwise
	 */
	default int toIdxIfPresent(int v) {
		int a = toIdx(v);
		return a < 0 || !contains(a) ? -1 : a;
	}

	/**
	 * Returns true if the specified value belongs to the current domain
	 * 
	 * @param v
	 *            a value
	 */
	default boolean containsValue(int v) {
		int a = toIdx(v);
		return a >= 0 && contains(a);
	}

	/**
	 * Returns true if the current domain has only one remaining value, whose index is specified.
	 * 
	 * @param a
	 *            an index (of value)
	 */
	default boolean containsOnly(int a) {
		return size() == 1 && contains(a);
	}

	/**
	 * Returns true if the current domain has only one remaining value, the one that is specified.
	 * 
	 * @param v
	 *            a value
	 */
	default boolean containsOnlyValue(int v) {
		return size() == 1 && v == toVal(first());
	}

	/**
	 * Returns the index of the unique value of the current domain. This is similar to first(), but with an assert/control.
	 */
	default int single() {
		assert size() == 1 : "Current size = " + size();
		return first();
	}

	/**
	 * Returns randomly the index of a value in the current domain.
	 */
	default int any() {
		return get(var().problem.head.random.nextInt(size()));
	}

	/**
	 * Returns the first present value.
	 */
	default int firstValue() {
		return toVal(first());
	}

	/**
	 * Returns the last present value.
	 */
	default int lastValue() {
		return toVal(last());
	}

	/**
	 * Returns the unique value of the current domain. This is similar to firstValue(), and lastValue(), but with an assert/control.
	 */
	default int singleValue() {
		return toVal(single());
	}

	/**
	 * Returns randomly a value of the current domain.
	 */
	default int anyValue() {
		return toVal(any());
	}

	/**
	 * Returns the smallest value of the initial domain
	 */
	default int smallestInitialValue() {
		return toVal(0);
	}

	/**
	 * Returns the greatest value of the initial domain
	 */
	default int greatestInitialValue() {
		return toVal(initSize() - 1);
	}

	/**
	 * Returns the difference between the second value and the first value of the domain (or 0 if only one present value)
	 */
	default int regretValue() {
		return size() <= 1 ? 0 : toVal(next(first())) - firstValue();
	}

	/**
	 * Returns the initial distance of the domain, that is the difference between the highest and smallest values
	 */
	default int initDistance() {
		return greatestInitialValue() - smallestInitialValue();
	}

	/**
	 * Returns the distance of the domain, that is the difference between the highest and smallest values
	 */
	default int distance() {
		return toVal(last()) - toVal(first());
	}

	/**
	 * Returns true if the domain is 0/1
	 */
	default boolean is01() {
		return initSize() == 2 && toVal(0) == 0 && toVal(1) == 1;
	}

	/**
	 * Returns a value present in both this domain and the specified one. There is no guarantee about the returned value (for example, it may not be the first
	 * possible one of the domain). If no common value is present, Integer.MAX_VALUE is returned.
	 * 
	 * @param dom
	 *            an other domain
	 * @return a value present in both the domain and the specified one, or Integer.MAX_VALUE
	 */
	default int commonValueWith(Domain dom) {
		if (size() <= dom.size())
			for (int a = first(); a != -1; a = next(a)) {
				int v = toVal(a);
				if (dom.containsValue(v))
					return v;
			}
		else
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int v = dom.toVal(a);
				if (containsValue(v))
					return v;
			}
		return Integer.MAX_VALUE;
	}

	/**
	 * Returns true if the domain and the specified one contain a common value
	 * 
	 * @param dom
	 *            an other domain
	 * @return true if the domain and the specified one contain a common value
	 */
	default boolean overlapWith(Domain dom) {
		return commonValueWith(dom) != Integer.MAX_VALUE;
	}

	/**
	 * Returns a value present in both this domain and the specified list of integers. There is no guarantee about the returned value (for example, it may not
	 * be the first possible one of the domain). If no common value is present, Integer.MAX_VALUE is returned.
	 * 
	 * @param values
	 *            a list of integers
	 * @return a value present in both the domain and the specified list of integers, or Integer.MAX_VALUE
	 */
	default int commonValueWith(int[] values) {
		if (size() <= values.length)
			for (int a = first(); a != -1; a = next(a)) {
				int v = toVal(a);
				if (Kit.isPresent(v, values))
					return v;
			}
		else
			for (int v : values)
				if (containsValue(v))
					return v;
		return Integer.MAX_VALUE;
	}

	/**
	 * Returns true if the domain and the specified list contain a common value
	 * 
	 * @param values
	 *            a list of integers
	 * @return true if the domain and the specified list contain a common value
	 */
	default boolean overlapWith(int[] values) {
		return commonValueWith(values) != Integer.MAX_VALUE;
	}

	/**
	 * Returns true if the (current) domain is a subset of the (current) specified one
	 * 
	 * @param dom
	 *            an other domain
	 * @return true if the (current) domain is a subset of the (current) specified one
	 */
	default boolean subsetOf(Domain dom) {
		for (int a = first(); a != -1; a = next(a))
			if (!dom.containsValue(toVal(a)))
				return false;
		return true;
	}

	/**
	 * Returns true is the (current) domain is a contiguous sequence of integers
	 * 
	 * @return true is the (current) domain is a contiguous sequence of integers
	 */
	default boolean connex() {
		return lastValue() - firstValue() + 1 == size();
	}

	/**
	 * Returns true if the (current) domain encloses the specified interval of values. The control is only performed at the bounds of the domain (which may
	 * contain some holes).
	 * 
	 * @param minValueIncluded
	 *            the minimal value of the interval (included)
	 * @param maxValueIncluded
	 *            the maximal value of the interval (included)
	 * @return true if the (current) domain encloses the specified interval of values
	 */
	default boolean enclose(int minValueIncluded, int maxValueIncluded) {
		return firstValue() <= minValueIncluded && maxValueIncluded <= lastValue();
	}

	/**
	 * Returns true if each value from the specified list belongs to the (current) domain
	 * 
	 * @param values
	 *            a list of values
	 * @return true if each value from the specified list belongs to the (current) domain
	 */
	default boolean enclose(int[] values) {
		assert IntStream.range(0, values.length).allMatch(i -> IntStream.range(i + 1, values.length).noneMatch(j -> values[i] == values[j]));
		if (size() < values.length)
			return false;
		for (int v : values)
			if (!containsValue(v))
				return false;
		return true;
	}

	/**
	 * Returns true if each value from the (current) domain belongs to the specified list
	 * 
	 * @param values
	 *            a list of values
	 * @return true if each value from the (current) domain belongs to the specified list
	 */
	default boolean enclosedIn(int[] values) {
		assert IntStream.range(0, values.length).allMatch(i -> IntStream.range(i + 1, values.length).noneMatch(j -> values[i] == values[j]));
		if (size() > values.length)
			return false;
		for (int a = first(); a != -1; a = next(a))
			if (!Kit.isPresent(toVal(a), values))
				return false;
		return true;
	}

	/**
	 * Returns true if the (current) domain exactly corresponds to to the specified list
	 * 
	 * @param values
	 *            a list of values
	 * @return true if the specified list gives the values of the current domain
	 */
	default boolean withExactlyTheseValues(int[] values) {
		assert IntStream.range(0, values.length).allMatch(i -> IntStream.range(i + 1, values.length).noneMatch(j -> values[i] == values[j]));
		if (size() != values.length)
			return false;
		for (int a = first(); a != -1; a = next(a))
			if (!Kit.isPresent(toVal(a), values))
				return false;
		return true;
	}

	/**
	 * Returns an array containing all values evaluated as true by the specified predicate.
	 * 
	 * @param p
	 *            a predicate for testing values
	 * @return an array containing all values verifying the specified predicate
	 */
	default int[] valuesChecking(Predicate<Integer> p) {
		List<Integer> values = new ArrayList<>();
		for (int a = first(); a != -1; a = next(a)) {
			int v = toVal(a);
			if (p.test(v))
				values.add(v);
		}
		return Kit.intArray(values);
	}

	default int indexOfValueClosestTo(int v) {
		int best = toIdxIfPresent(v);
		if (best != -1)
			return best;
		int bestDistance = Integer.MAX_VALUE;
		for (int a = first(); a != -1; a = next(a)) {
			int dist = Math.abs(v - toVal(a));
			if (dist < bestDistance) {
				best = a;
				bestDistance = dist;
			} else
				break;
		}
		return best;

	}

	default int indexOfValueFarthestTo(int v) {
		return v - firstValue() > lastValue() - v ? first() : last();

	}

	/**********************************************************************************************
	 * Methods for updating the domain (i.e., removing values)
	 *********************************************************************************************/

	default boolean handleReduction() {
		return var().problem.solver.propagation.handleReduction(var());
	}

	/**
	 * Removes at construction time (hence, definitively) the value at the specified index. <br />
	 * Important: this method must only called when building the problem.
	 * 
	 * @param a
	 *            a value index
	 */
	default void removeAtConstructionTime(int a) {
		// System.out.println("removing " + var() + "=" + toVal(a) + (a != toVal(a) ? " (index " + a + ")" : "") + " at construction time");
		Problem problem = var().problem;
		control(problem.solver == null, () -> "Must be called before the solver being built.");
		remove(a, 0);
		problem.nValueRemovals++;
		problem.features.nValuesRemovedAtConstructionTime++;
	}

	/**
	 * Removes at construction time (hence, definitively) every value whose index is tested as true by the specified predicate. <br />
	 * Important: this method must only called when building the problem.
	 * 
	 * @param p
	 *            a predicate for testing value indexes
	 */
	default void removeAtConstructionTime(Predicate<Integer> p) {
		for (int a = first(); a != -1; a = next(a))
			if (p.test(a))
				removeAtConstructionTime(a);
	}

	/**
	 * Removes at construction time (hence, definitively) the specified value. <br />
	 * Important: this method must only called when building the problem.
	 * 
	 * @param v
	 *            a value
	 */
	default void removeValueAtConstructionTime(int v) {
		int a = toIdx(v);
		if (a != -1)
			removeAtConstructionTime(a);
	}

	/**
	 * Removes at construction time (hence, definitively) every value tested as true by the specified predicate. <br />
	 * Important: this method must only called when building the problem.
	 * 
	 * @param p
	 *            a predicate for testing values
	 */
	default void removeValuesAtConstructionTime(Predicate<Integer> p) {
		for (int a = first(); a != -1; a = next(a))
			if (p.test(toVal(a)))
				removeAtConstructionTime(a);
	}

	/**
	 * Method to call when elementary calls for removing some values may have been executed (i.e., calls to removeElementary) in order to take it into account
	 * for propagation.
	 * 
	 * @param sizeBefore
	 *            the size of the domain before elementary calls
	 * @return false if an inconsistency is detected
	 */
	default boolean afterElementaryCalls(int sizeBefore) {
		return size() == sizeBefore ? true : handleReduction();
	}

	/**
	 * Removes the value at the specified index. The value is assumed to be present, and the variable to which the domain is attached is assumed to be future
	 * (i.e. non explicitly assigned). <br />
	 * Important: the management of this removal with respect to propagation is not handled: removal is said elementary.
	 * 
	 * @param a
	 *            a value index
	 */
	default void removeElementary(int a) {
		// System.out.println("removing " + var() + "=" + toVal(a) + (a != toVal(a) ? " (index " + a + ")" : "") + " from "
		// + var().problem.solver.propagation.currFilteringCtr);
		Variable x = var();
		assert !x.assigned() && contains(a) : x + " " + x.assigned() + " " + contains(a);
		Solver solver = x.problem.solver;
		int depth = solver.stackVariable(x);
		// stacking variables (to keep track of propagation) must always be performed before domain reduction
		remove(a, depth);
		for (ObserverOnRemovals observer : solver.observersOnRemovals)
			observer.afterRemoval(x, a);
		x.problem.nValueRemovals++;
	}

	/**
	 * Removes the value at the specified index. The value is assumed to be present. It returns false if an inconsistency is detected (because this is the index
	 * of the last value of the domain). <br />
	 * Important: the management of this removal with respect to propagation is handled.
	 * 
	 * @param a
	 *            a value index
	 * @return false if an inconsistency is detected
	 */
	default boolean remove(int a) {
		assert contains(a);
		if (size() == 1)
			return fail();
		removeElementary(a);
		return handleReduction();
	}

	/**
	 * Removes the value at the specified index, if present. It returns false if an inconsistency is detected (because this is the index of the last value of
	 * the domain). <br />
	 * Important: the management of this removal with respect to propagation is handled.
	 * 
	 * @param a
	 *            a value index
	 * @return false if an inconsistency is detected
	 */
	default boolean removeIfPresent(int a) {
		return !contains(a) || remove(a);
	}

	/**
	 * Removes each index whose corresponding flag is false in the specified array. The number of removed indexes is given by the second argument. The
	 * management of these removals with respect to propagation is handled.
	 * 
	 * @param flags
	 *            an array of flags indicating which indexes must be removed (when false)
	 * @param nRemovals
	 *            the number of indexes to be removed
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean remove(boolean[] flags, int nRemovals) {
		assert 0 < nRemovals && nRemovals <= size() && flags.length == initSize()
				&& IntStream.range(0, initSize()).filter(a -> contains(a) && !flags[a]).count() == nRemovals;
		if (size() == nRemovals)
			return fail();
		for (int cnt = 0, a = first(); cnt < nRemovals; a = next(a))
			if (!flags[a]) {
				removeElementary(a);
				cnt++;
			}
		return handleReduction();
	}

	/**
	 * Removes the values at the indexes given in the specified set. If the specified boolean is set to true, a test is performed to only consider values that
	 * are present in the current domain. The management of these removals with respect to propagation is handled.
	 * 
	 * @param idxs
	 *            a dense set with indexes of values
	 * @param testPresence
	 *            when true, the presence of values is tested first
	 * @return false if an inconsistency is detected
	 */
	default boolean remove(SetDense idxs, boolean testPresence) {
		int sizeBefore = size();
		if (testPresence) {
			int nRemaining = sizeBefore;
			for (int i = idxs.limit; i >= 0; i--)
				if (contains(idxs.dense[i])) {
					if (nRemaining == 1)
						return fail();
					removeElementary(idxs.dense[i]);
				}
			return afterElementaryCalls(sizeBefore);
		}
		assert IntStream.range(0, idxs.size()).allMatch(i -> contains(idxs.dense[i]));
		if (idxs.size() == 0)
			return true;
		if (idxs.size() == sizeBefore)
			return fail();
		for (int i = idxs.limit; i >= 0; i--)
			removeElementary(idxs.dense[i]);
		return handleReduction();
	}

	/**
	 * Removes the values at the indexes given in the specified set. It is assumed that all these values are currently present in the domain.The management of
	 * these removals with respect to propagation is handled.
	 * 
	 * @param idxs
	 *            a dense set with indexes of values
	 * @return false if an inconsistency is detected
	 */
	default boolean remove(SetDense idxs) {
		return remove(idxs, false);
	}

	/**
	 * Reduces the domain at the value at the specified index. The value is assumed to be present. <br />
	 * Important: the management of this removal with respect to propagation is not handled.
	 * 
	 * @param a
	 *            a value index
	 * @return the number of removed values
	 */
	default int reduceToElementary(int a) {
		assert contains(a) : a + " is not present";
		if (size() == 1)
			return 0; // 0 removal
		Variable x = var();
		Solver solver = x.problem.solver;
		int depth = solver.stackVariable(x);
		// stacking variables must always be performed before domain reduction
		int nRemovals = reduceTo(a, depth);
		for (ObserverOnRemovals observer : solver.observersOnRemovals)
			observer.afterRemovals(x, nRemovals);
		x.problem.nValueRemovals += nRemovals;
		assert nRemovals >= 0 && size() == 1 : "nRemovals: " + nRemovals + " size:" + size();
		return nRemovals;
	}

	/**
	 * Removes any value whose index is different from the specified index. <br />
	 * Important: the value at the specified index is not necessarily present in the domain. In that case, false is returned.
	 * 
	 * @param a
	 *            a value index
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean reduceTo(int a) {
		return !contains(a) ? fail() : reduceToElementary(a) == 0 || handleReduction();
	}

	/**
	 * Removes the values that are different from the specified value. <br />
	 * Important: the specified value is not necessarily present in the domain.
	 *
	 * @param v
	 *            a value
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean reduceToValue(int v) {
		int a = toIdxIfPresent(v);
		return a == -1 ? fail() : reduceToElementary(a) == 0 || handleReduction();
	}

	/**
	 * Forces failure (inconsistency)
	 * 
	 * @return false
	 */
	default boolean fail() {
		return var().problem.solver.propagation.handleReduction(var(), 0);
	}

	/**
	 * Removes the specified value. <br />
	 * Important: the value is assumed to be present.
	 * 
	 * @param v
	 *            a value
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValue(int v) {
		int a = toIdxIfPresent(v);
		assert a != -1;
		return remove(a);
	}

	/**
	 * Removes the specified value, if present. If the value is not present, the method returns true (non aggressive mode). Otherwise, false is returned if an
	 * inconsistency is detected (domain wipe-out).
	 * 
	 * @param v
	 *            a value
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValueIfPresent(int v) {
		int a = toIdxIfPresent(v);
		return a == -1 || remove(a);
	}

	/**
	 * Removes all values that are less than or equal to the specified limit
	 * 
	 * @param limit
	 *            an int used as limit
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesLE(int limit) {
		if (lastValue() <= limit)
			return fail();
		int sizeBefore = size();
		for (int a = first(); a != -1 && toVal(a) <= limit; a = next(a))
			removeElementary(a);
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are greater than or equal to the specified limit
	 * 
	 * @param limit
	 *            an int used as limit
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesGE(int limit) {
		if (firstValue() >= limit)
			return fail();
		int sizeBefore = size();
		for (int a = last(); a != -1 && toVal(a) >= limit; a = prev(a))
			removeElementary(a);
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are strictly less than the specified limit
	 * 
	 * @param limit
	 *            an int used as limit
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesLT(int limit) {
		return removeValuesLE(limit != Integer.MIN_VALUE ? limit - 1 : limit);
	}

	/**
	 * Removes all values that are strictly greater than the specified limit
	 * 
	 * @param limit
	 *            an int used as limit
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesGT(int limit) {
		return removeValuesGE(limit != Integer.MAX_VALUE ? limit + 1 : limit);
	}

	/**
	 * Removes all values that are strictly less than the specified limit (long)
	 * 
	 * @param limit
	 *            a long used as limit
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesLT(long limit) {
		assert limit != Long.MIN_VALUE;
		limit--;
		return removeValuesLE(limit <= Integer.MIN_VALUE ? Integer.MIN_VALUE : limit >= Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) limit);
	}

	/**
	 * Removes all values that are strictly greater than the specified limit (long)
	 * 
	 * @param limit
	 *            a long used as limit
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesGT(long limit) {
		assert limit != Long.MAX_VALUE;
		limit++;
		return removeValuesGE(limit <= Integer.MIN_VALUE ? Integer.MIN_VALUE : limit >= Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) limit);
	}

	/**
	 * Removes all values that, when multiplied by the specified coefficient, verify the condition defined by the specified relational operator and the
	 * specified limit
	 * 
	 * @param type
	 *            the relational operator used for the condition
	 * @param limit
	 *            a long used as limit for the condition
	 * @param coeff
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValues(TypeOperatorRel type, long limit, int coeff) {
		assert coeff != 0 && limit != Long.MIN_VALUE && limit != Long.MAX_VALUE;
		if (type == LT) {
			type = LE;
			limit--;
		} else if (type == GT) {
			type = GE;
			limit++;
		}
		if (coeff < 0) {
			coeff = -coeff;
			type = type.arithmeticInversion();
			limit = -limit;
		}
		long newLimit = (Math.abs(limit) / coeff) * (limit < 0 ? -1 : 1);
		if (limit > 0 && type == GE && limit % coeff != 0)
			newLimit++;
		if (limit < 0 && type == LE && -limit % coeff != 0)
			newLimit--;
		return type == LE ? removeValuesLE(Kit.round(newLimit)) : removeValuesGE(Kit.round(newLimit));
	}

	default boolean removeValuesModIn(Domain dom, int coeff) {
		int sizeBefore = size();
		if (sizeBefore == 1)
			return !dom.containsValue(firstValue() % coeff) || fail();
		for (int a = first(); a != -1; a = next(a))
			if (dom.containsValue(toVal(a) % coeff))
				removeElementary(a);
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValuesAtDistanceGT(int k, Domain dom) {
		int sizeBefore = size();
		boolean overk = k * 2 < dom.size();
		extern: for (int a = first(); a != -1; a = next(a)) {
			int va = toVal(a);
			if (dom.containsValue(va)) // distance 0
				continue;
			if (overk) {
				for (int i = 1; i <= k; i++)
					if (dom.containsValue(va + k) || dom.containsValue(va - k))
						continue extern;
			} else
				for (int b = dom.first(); b != -1; b = dom.next(b))
					if (Math.abs(va - dom.toVal(b)) <= k)
						continue extern;
			removeElementary(a);
		}
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValuesNumeratorsGT(int k, int denominator) {
		int sizeBefore = size();
		for (int a = last(); a != -1; a = prev(a)) {
			int va = toVal(a);
			if (va / denominator > k)
				removeElementary(a);
			else
				break;
		}
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValuesDenominatorsGT(int k, int numerator) {
		assert !containsValue(0);
		int sizeBefore = size();
		for (int a = first(); a != -1; a = next(a)) {
			int va = toVal(a);
			if (numerator / va > k)
				removeElementary(a);
			else
				break;
		}
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValuesNumeratorsLT(int k, int denominator) {
		int sizeBefore = size();
		for (int a = first(); a != -1; a = next(a)) {
			int va = toVal(a);
			if (va / denominator < k)
				removeElementary(a);
			else
				break;
		}
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValuesDenominatorsLT(int k, int numerator) {
		int sizeBefore = size();
		for (int a = last(); a != -1; a = prev(a)) {
			int va = toVal(a);
			if (numerator / va < k)
				removeElementary(a);
			else
				break;
		}
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are present in the specified domain, and returns false if the domain becomes empty.
	 * 
	 * @param dom
	 *            another domain
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesIn(Domain dom) {
		int sizeBefore = size();
		if (sizeBefore == 1)
			return !dom.containsValue(firstValue()) || fail();
		if (size() < dom.size()) {
			for (int a = first(); a != -1; a = next(a))
				if (dom.containsValue(toVal(a)))
					removeElementary(a);
		} else {
			for (int b = dom.first(); b != -1; b = dom.next(b))
				if (containsValue(dom.toVal(b)))
					removeElementary(toIdx(dom.toVal(b)));
		}
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are not present in the specified domain, and returns false if the domain becomes empty.
	 * 
	 * @param dom
	 *            another domain
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesNotIn(Domain dom) {
		if (lastValue() < dom.firstValue() || dom.lastValue() < firstValue())
			return fail();
		int sizeBefore = size();
		if (sizeBefore == 1) // keep it for assigned variables
			return dom.containsValue(firstValue()) || fail();
		for (int a = first(); a != -1; a = next(a))
			if (!dom.containsValue(toVal(a)))
				removeElementary(a);
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeSurplusValuesWrt(Domain dom) {
		assert size() > dom.size() && dom.subsetOf(this); // we also assume that all values in dom are contained in this domain
		int sizeBefore = size();
		for (int a = first(); a != -1; a = next(a))
			if (!dom.containsValue(toVal(a))) {
				removeElementary(a);
				if (size() == dom.size())
					break;
			}
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are present in the specified set, and returns false if the domain becomes empty.
	 * 
	 * @param set
	 *            a set of integers
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesIn(Set<Integer> set) {
		int sizeBefore = size();
		if (sizeBefore == 1)
			return !set.contains(firstValue()) || fail();
		if (size() < set.size()) {
			for (int a = first(); a != -1; a = next(a))
				if (set.contains(toVal(a)))
					removeElementary(a);
		} else {
			for (int v : set)
				if (containsValue(v)) {
					removeElementary(toIdx(v));
					if (size() == 0)
						break;
				}
		}
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are not present in the specified set, and returns false if the domain becomes empty.
	 * 
	 * @param set
	 *            a set of integers
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesNotIn(Set<Integer> set) {
		int sizeBefore = size();
		if (sizeBefore == 1)
			return set.contains(firstValue()) || fail();
		for (int a = first(); a != -1; a = next(a))
			if (set.contains(toVal(a)) == false)
				removeElementary(a);
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are present in the specified array, and returns false if the domain becomes empty. <br />
	 * 
	 * @param set
	 *            an array of integers
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesIn(int[] set) {
		int sizeBefore = size(), cnt = 0;
		for (int i = set.length - 1; i >= 0; i--) {
			int v = set[i];
			if (containsValue(v)) {
				if (size() == 1)
					return fail();
				removeElementary(toIdx(v));
				if (++cnt == sizeBefore)
					break; // since all values of the domain have been considered
			}
		}
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are not present in the specified array, and returns false if the domain becomes empty. <br />
	 * VERY IMPORTANT: the specified set must be increasingly ordered.
	 * 
	 * @param set
	 *            an array of integers
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesNotIn(int[] set) {
		assert Kit.isStrictlyIncreasing(set);
		int sizeBefore = size();
		if (sizeBefore == 1)
			return Arrays.binarySearch(set, firstValue()) >= 0 || fail();
		int i = 0;
		for (int a = first(); a != -1; a = next(a)) {
			int v = toVal(a);
			while (i < set.length && v > set[i])
				i++;
			if (i == set.length || v != set[i])
				removeElementary(a);
		}
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are present in the specified dense set, and returns false if the domain becomes empty.
	 * 
	 * @param set
	 *            a dense set
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesIn(SetDense set) {
		int sizeBefore = size(), cnt = 0;
		for (int i = set.limit; i >= 0; i--) {
			int v = set.dense[i];
			if (containsValue(v)) {
				if (size() == 1)
					return fail();
				removeElementary(toIdx(v));
				if (++cnt == sizeBefore)
					break; // since all values of the domain have been considered
			}
		}
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are present in the specified range, and returns false if the domain becomes empty.
	 * 
	 * @param start
	 *            the lower bound (inclusive) of the range
	 * @param stop
	 *            the upper bound (exclusive) of the range
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesInRange(int start, int stop) {
		if (start >= stop)
			return true;
		int first = firstValue(), last = lastValue();
		if (start > last || stop < first)
			return true; // because there is no overlapping
		int left = Math.max(start, first), right = Math.min(stop - 1, last);
		if (left == first) {
			if (right == last)
				return fail(); // because the domain is contained in the range
		} else if (!containsValue(left)) { // we know that first < start <= last, and start < stop, so start <= right
			// finding the first value in the domain contained in the range
			if (size() < (right - left))
				for (int a = first(); a != -1; a = next(a)) {
					left = toVal(a);
					if (left >= start)
						break;
				}
			else {
				left++;
				while (!containsValue(left) && left <= right)
					left++;
			}
		}
		if (left > right)
			return true;
		int sizeBefore = size();
		for (int a = toIdx(left); a != -1; a = next(a)) {
			left = toVal(a);
			if (left > right)
				break;
			removeValue(left);
		}
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all indexes evaluated as true by the specified predicate, and returns false if the domain becomes empty.
	 * 
	 * @param p
	 *            a predicate for testing value indexes
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeIndexesChecking(Predicate<Integer> p) {
		int sizeBefore = size();
		if (sizeBefore == 1)
			return !p.test(first()) || fail();
		for (int a = first(); a != -1; a = next(a))
			if (p.test(a))
				removeElementary(a);
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values evaluated as true by the specified predicate, and returns false if the domain becomes empty.
	 * 
	 * @param p
	 *            a predicate for testing values
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesChecking(Predicate<Integer> p) {
		int sizeBefore = size();
		if (sizeBefore == 1)
			return !p.test(firstValue()) || fail();
		for (int a = first(); a != -1; a = next(a))
			if (p.test(toVal(a)))
				removeElementary(a);
		return afterElementaryCalls(sizeBefore);
	}

	/**********************************************************************************************
	 * Control and Display
	 *********************************************************************************************/

	/**
	 * Returns either an object Range or an array with all values of the initial domain
	 * 
	 * @return an object Range or an int array
	 */
	Object allValues();

	/**
	 * Returns a pretty string form of the specified value
	 * 
	 * @param v
	 *            value
	 * @return a pretty form of the specified value
	 */
	default String prefixForVal(int v) {
		if (!var().problem.head.control.general.jsonQuotes && var().id.chars().filter(ch -> ch == '[').count() >= 2) {
			int min = toVal(0), max = toVal(initSize() - 1);
			if (min >= 0) {
				if (max > 9) {
					if (max < 100)
						return v < 10 ? " " : "";
					else if (max < 1000)
						return v < 10 ? "  " : v < 100 ? " " : "";
				}
			} else {
				if (-10 < min && max < 10)
					return v < 0 ? "" : " ";
				if (-10 < min && max < 100)
					return v < 0 ? "" : v < 10 ? " " : "";
				if (-10 < min && max < 1000)
					return v < 0 ? " " : v < 10 ? "  " : v < 100 ? " " : "";
			}
		}
		return "";
	}

	/**
	 * Returns a pretty string form of the value whose index is specified
	 * 
	 * @param a
	 *            index of value
	 * @return a pretty form of the value whose index is specified
	 */
	default String prettyValueOf(int a) {
		int v = toVal(a);
		// System.out.println("pretty " + a + " " + v);
		return prefixForVal(v) + v;
		// if (!var().problem.head.control.general.jsonQuotes && var().id.chars().filter(ch -> ch == '[').count() >= 2) {
		// int min = toVal(0), max = toVal(initSize() - 1);
		// if (min >= 0) {
		// if (max > 9) {
		// if (max < 100)
		// return (v < 10 ? " " : "") + v;
		// else if (max < 1000)
		// return (v < 10 ? " " : v < 100 ? " " : "") + v;
		// }
		// } else {
		// if (min > -10 && max < 10)
		// return (v < 0 ? "" : " ") + v;
		// }
		// }
		// return v + "";
	}

	/**
	 * Returns a string listing the values of the current domain. Note that intervals are used when appropriate.
	 * 
	 * @return a string listing the values of the current domain
	 */
	default String stringOfCurrentValues() {
		if (size() == 0)
			return "";
		StringBuilder sb = new StringBuilder();
		int prev = firstValue(), intervalMin = prev;
		for (int a = next(first()); a != -1; a = next(a)) {
			int v = toVal(a);
			if (v != prev + 1) { // note: when only two values, no need for an interval
				sb.append(prev == intervalMin ? prev : intervalMin + (prev == intervalMin + 1 ? " " : "..") + prev).append(" ");
				intervalMin = v;
			}
			prev = v;
		}
		return sb.append(prev == intervalMin ? prev : intervalMin + (prev == intervalMin + 1 ? " " : "..") + prev).toString();
	}

	default String stringOfRemovedValues() {
		if (nRemoved() == 0)
			return "";
		StringBuilder sb = new StringBuilder();
		sb.append("#").append(nRemoved() + " --> ");
		int a = 0;
		while (a < initSize()) {
			while (a < initSize() && contains(a))
				a++;
			if (a == initSize())
				break;
			int b = a + 1;
			while (b < initSize() && !contains(b))
				b++;
			if (b == a + 1)
				sb.append(toVal(a)).append(" ");
			else
				sb.append(toVal(a)).append("..").append(toVal(b - 1)).append(" ");
			a = b;
		}
		return sb.toString();
	}

	/**
	 * Prints a description of the domain. Detailed information is given if the specified boolean is true
	 * 
	 * @param mode
	 *            0, 1 or 2 according to the desired detail
	 */
	default void display(int mode) {
		if (mode == 0)
			System.out.println("  Domain " + this + " : " + stringOfCurrentValues());
		if (mode >= 1) {
			System.out.println("  Domain " + this + " (imv=" + indexesMatchValues() + ", typeIdentifier=" + typeIdentifier() + ")");
			System.out.println("\t initSize=" + initSize() + " and size=" + size());
			if (size() != 0)
				System.out.println("\t first=" + firstValue() + (indexesMatchValues() ? "" : "(" + first() + ")") + " and last=" + lastValue()
						+ (indexesMatchValues() ? "" : "(" + last() + ")"));
			if (mode == 2)
				System.out.println("\t values = {" + stringOfCurrentValues() + "}" + "\nStructures\n" + stringOfStructures());
		}
	}

}
