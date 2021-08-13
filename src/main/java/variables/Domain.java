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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Range;
import org.xcsp.common.Types.TypeOperatorRel;

import interfaces.Observers.ObserverOnDomainReductions;
import problem.Problem;
import propagation.Propagation;
import sets.SetDense;
import sets.SetLinked;
import utility.Kit;

/**
 * A domain for a variable (from a constraint network) is composed of a set of integer values. The domain is initially full, but typically reduced when
 * logically reasoning (with constraints). When handling a domain, to simplify programming, one usually iterates over the indexes of the values; if the domains
 * contains d values, the indexes range from 0 to d-1. For instance, if the domain is the set of values <code> {1,4,5} </code>, their indexes are respectively
 * <code> {0,1,2} </code>. The correspondence between indexes of values and values is given by the methods <code> toIdx </code> and <code> toVal </code>.
 *
 * @author Christophe Lecoutre
 *
 */
public interface Domain extends SetLinked {

	/**********************************************************************************************
	 * Static Members
	 *********************************************************************************************/

	static final int TAG_RANGE = Integer.MAX_VALUE;
	static final int TAG_SYMBOLS = Integer.MAX_VALUE - 1;

	/**
	 * The cache used for storing type identifiers.
	 */
	static final List<int[]> types = new ArrayList<int[]>();

	/**
	 * Returns a type identifier for the specified array of values (integers), while using a cache.
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

	static void setMarks(Variable[] variables) {
		for (Variable x : variables)
			x.dom.setMark();
	}

	static void restoreAtMarks(Variable[] variables) {
		for (Variable x : variables)
			x.dom.restoreAtMark();
	}

	/**
	 * Returns the number of valid tuples
	 * 
	 * @param doms
	 *            an array of domains
	 * @param usingInitSize
	 *            indicates if the initial size of the domains must be considered (or the current size)
	 * @return the number of valid tuples
	 */
	static BigInteger nValidTuples(Domain[] doms, boolean usingInitSize) {
		BigInteger prod = BigInteger.ONE;
		for (Domain dom : doms)
			prod = prod.multiply(BigInteger.valueOf(usingInitSize ? dom.initSize() : dom.size()));
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
			int size = doms[i].size(); // generalizing with a parameter (usingInitSize)?
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

	/**********************************************************************************************
	 * Class Members
	 *********************************************************************************************/

	default boolean areInitValuesExactly(Range range) {
		control(range.step == 1);
		return initSize() == range.length() && IntStream.range(0, initSize()).allMatch(a -> toVal(a) == range.start + a);
	}

	default boolean areInitValuesSubsetOf(int[] values) {
		return initSize() <= values.length && IntStream.range(0, initSize()).allMatch(a -> Kit.isPresent(toVal(a), values));
	}

	default boolean areInitValuesSubsetOf(Range range) {
		control(range.step == 1);
		return initSize() <= range.length() && IntStream.range(0, initSize()).allMatch(a -> range.start <= toVal(a) && toVal(a) < range.stop);
	}

	/**
	 * Returns the variable to which the domain is attached.
	 */
	Variable var();

	/**
	 * Returns the type identifier of the domain. Similar domains share the same type identifier.
	 * 
	 * @return the type identifier of the domain
	 */
	int typeIdentifier();

	default String typeName() {
		return "D" + typeIdentifier();
	}

	/**
	 * Returns the propagation object behind the scene.
	 */
	Propagation propagation();

	void setPropagation(Propagation propagation);

	/**
	 * Indicates if indexes (of values) and values match, i.e. if for every index a, we have toVal(a) = a, and for every value v, we have toIdx(v)=v.
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
	 * Returns the value at the specified index
	 * 
	 * @param a
	 *            a value index
	 * @return the value at the specified index
	 */
	int toVal(int a);

	/**
	 * Returns the index of the specified value if the value belongs to the current domain, -1 otherwise.
	 * 
	 * @param v
	 *            a value
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
	 *            a value index
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
	 * Returns the index of the unique value of the domain. This is similar to first(), but with an assert/control.
	 */
	default int single() {
		assert size() == 1 : "Current size = " + size();
		return first();
	}

	/**
	 * Returns randomly the index of a value in the domain.
	 */
	default int any() {
		return get(propagation().solver.head.random.nextInt(size()));
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
	 * Returns the unique value of the domain. This is similar to firstValue(), and lastValue(), but with an assert/control.
	 */
	default int singleValue() {
		return toVal(single());
	}

	/**
	 * Returns randomly a value of the domain.
	 */
	default int anyValue() {
		return toVal(any());
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
				int va = toVal(a);
				if (dom.containsValue(va))
					return va;
			}
		else
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int va = dom.toVal(a);
				if (containsValue(va))
					return va;
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
		return this.commonValueWith(dom) != Integer.MAX_VALUE;
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
	 * Returns an array containing all values evaluated as true by the specified predicate.
	 * 
	 * @param p
	 *            a predicate for testing values
	 * @return an array containing all values verifying the specified predicate
	 */
	default int[] valuesChecking(Predicate<Integer> p) {
		List<Integer> values = new ArrayList<>();
		for (int a = first(); a != -1; a = next(a)) {
			int va = toVal(a);
			if (p.test(va))
				values.add(va);
		}
		return Kit.intArray(values);
	}

	/**********************************************************************************************
	 * Methods for updating the domain (i.e., removing values)
	 *********************************************************************************************/

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
		removeAtConstructionTime(toIdx(v));
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

	default boolean afterElementaryCalls(int sizeBefore) {
		return size() == sizeBefore ? true : propagation().handleReduction(var());
	}

	/**
	 * Removes the value at the specified index. <br />
	 * The value is assumed to be present, and the variable to which the domain is attached is assumed to be future (i.e. non explicitly assigned). <br />
	 * Important: the management of this removal with respect to propagation is not handled: removal is said elementary.
	 * 
	 * @param a
	 *            a value index
	 */
	default void removeElementary(int a) {
		// System.out.println("removing " + var() + "=" + toVal(a) + (a != toVal(a) ? " (index " + a + ")" : "") + " from " + propagation().currFilteringCtr);
		Variable x = var();
		assert !x.assigned() && contains(a) : x + " " + x.assigned() + " " + contains(a);
		int depth = propagation().solver.stackVariable(x); // stacking variables (to keep track of propagation) must always be performed before domain reduction
		remove(a, depth);
		for (ObserverOnDomainReductions observer : x.problem.observersDomainReduction)
			observer.afterRemoval(x, a);
		x.problem.nValueRemovals++;
	}

	/**
	 * Removes the value at the specified index. <br />
	 * The value is assumed to be present. <br />
	 * Returns false if an inconsistency is detected (because this is the index of the last value of the domain). <br />
	 * The management of this removal with respect to propagation is handled.
	 */
	default boolean remove(int a) {
		assert contains(a);
		if (size() == 1)
			return fail();
		removeElementary(a);
		return propagation().handleReduction(var());
	}

	/**
	 * Removes the value at the specified index, if present.<br />
	 * Returns false if an inconsistency is detected (because this is the index of the last value of the domain). <br />
	 * But if the index is not present, returns true (non aggressive mode). <br />
	 * The management of this removal with respect to propagation is handled.
	 */
	default boolean removeIfPresent(int a) {
		return !contains(a) || remove(a);
	}

	/**
	 * Removes the values (at the indexes) given by the specified array of flags. <br>
	 * When a flag is set to false, this means that the corresponding value must be removed. <br />
	 * Returns false if an inconsistency is detected. <br />
	 * The management of these removals with respect to propagation is handled.
	 */

	/**
	 * Removes each index whose corresponding flag is true in the specified array. The number of removed indexes is given by the second argument.
	 * 
	 * @param flags
	 *            an array of flags indicating which indexes must be removed
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
		return propagation().handleReduction(var());
	}

	/**
	 * Removes the values at the indexes given in the specified set. <br />
	 * If the specified boolean is set to true, a test is performed to only consider values that are present in the current domain. <br />
	 * Returns false if an inconsistency is detected. <br />
	 * The management of these removals with respect to propagation is handled.
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
		} else {
			assert IntStream.range(0, idxs.size()).allMatch(i -> contains(idxs.dense[i]));
			if (idxs.size() == 0)
				return true;
			if (idxs.size() == sizeBefore)
				return fail();
			for (int i = idxs.limit; i >= 0; i--)
				removeElementary(idxs.dense[i]);
			return propagation().handleReduction(var());
		}
	}

	/**
	 * Removes the values at the indexes given in the specified set. <br />
	 * It is assumed that all these values are currently present in the domain. <br />
	 * Returns false if an inconsistency is detected. <br />
	 * The management of these removals with respect to propagation is handled.
	 */
	default boolean remove(SetDense idxs) {
		return remove(idxs, false);
	}

	/**
	 * Reduces the domain at the value at the specified index. <br />
	 * The value is assumed to be present. <br />
	 * Returns the number of removed values.<br />
	 * Important: the management of this removal with respect to propagation is not handled.
	 */
	default int reduceToElementary(int a) {
		assert contains(a) : a + " is not present";
		if (size() == 1)
			return 0; // 0 removal
		Variable x = var();
		int depth = propagation().solver.stackVariable(x); // stacking variables must always be performed before domain reduction
		int nRemovals = reduceTo(a, depth);
		for (ObserverOnDomainReductions observer : x.problem.observersDomainReduction)
			observer.afterRemovals(x, nRemovals);
		x.problem.nValueRemovals += nRemovals;
		assert nRemovals >= 0 && size() == 1 : "nRemovals: " + nRemovals + " size:" + size();
		return nRemovals;
	}

	/**
	 * Removes any value whose index is different from the specified index. <br />
	 * Returns false if an inconsistency is detected (domain wipe-out). <br />
	 * Important: the value at the specified index is not necessarily present in the domain. <br />
	 * In that case, false is returned.
	 * 
	 * @param a
	 *            a value index
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean reduceTo(int a) {
		return !contains(a) ? fail() : reduceToElementary(a) == 0 || propagation().handleReduction(var());
	}

	/**
	 * Removes the values that are different from the specified value. <br />
	 * Returns false if an inconsistency is detected (domain wipe-out). <br />
	 * Important: the specified value is not necessarily present in the domain.
	 *
	 * @param v
	 *            a value
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean reduceToValue(int v) {
		int a = toIdxIfPresent(v);
		return a == -1 ? fail() : reduceToElementary(a) == 0 || propagation().handleReduction(var());
	}

	/**
	 * Forces failure (inconsistency)
	 * 
	 * @return false
	 */
	default boolean fail() {
		return propagation().handleReduction(var(), 0);
	}

	/**
	 * Removes the specified value. <br />
	 * Important: the value is assumed to be present. <br />
	 * Returns false if an inconsistency is detected (domain wipe-out). <br />
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
	 * Removes the specified value, if present. <br />
	 * If the value is not present, the method returns true (non aggressive mode). <br />
	 * Otherwise, false is returned if an inconsistency is detected (domain wipe-out). <br />
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
		return type == LE ? removeValuesLE(Kit.trunc(newLimit)) : removeValuesGE(Kit.trunc(newLimit));
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
	 * IMPORTANT: the specified set must be increasingly ordered.
	 * 
	 * @param set
	 *            an array of integers
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesIn(int[] set) {
		assert Kit.isStrictlyIncreasing(set);
		int sizeBefore = size();
		if (sizeBefore == 1)
			return Arrays.binarySearch(set, firstValue()) < 0 || fail();
		for (int i = set.length - 1; i >= 0; i--) {
			int v = set[i];
			if (containsValue(v)) {
				removeElementary(toIdx(v));
				if (size() == 0)
					break;
			}
		}
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are not present in the specified array, and returns false if the domain becomes empty. <br />
	 * IMPORTANT: the specified set must be increasingly ordered.
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
			int va = toVal(a);
			while (i < set.length && va > set[i])
				i++;
			if (i == set.length || va != set[i])
				removeElementary(a);
		}
		return afterElementaryCalls(sizeBefore);
	}

	/**
	 * Removes all values that are present in the specified dense set, and returns false if the domain becomes empty. <br />
	 * IMPORTANT: the specified set must be increasingly ordered.
	 * 
	 * @param set
	 *            a dense set
	 * @return false if an inconsistency (empty domain) is detected
	 */
	default boolean removeValuesIn(SetDense set) {
		assert set.isStrictlyIncreasing();
		int sizeBefore = size();
		if (sizeBefore == 1)
			return Arrays.binarySearch(set.dense, 0, set.size(), firstValue()) < 0 || fail();
		for (int i = set.limit; i >= 0; i--) {
			int v = set.dense[i];
			if (containsValue(v)) {
				removeElementary(toIdx(v));
				if (size() == 0)
					break;
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
	 * Returns a pretty string form of the value whose index is specified
	 * 
	 * @param a
	 *            index of value
	 * @return a pretty form of the value whose index is specified
	 */
	default String prettyValueOf(int a) {
		return toVal(a) + "";
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

	/**
	 * Prints a description of the domain. Detailed information is given if the specified boolean is true
	 * 
	 * @param exhaustively
	 *            a boolean used for getting more information
	 */
	default void display(boolean exhaustively) {
		System.out.println("  Domain " + this + " (imv=" + indexesMatchValues() + ", typeIdentifier=" + typeIdentifier() + ")");
		System.out.println("\t initSize=" + initSize() + " and size=" + size());
		if (size() != 0)
			System.out.println("\t first=" + firstValue() + (indexesMatchValues() ? "" : "(" + first() + ")") + " and last=" + lastValue()
					+ (indexesMatchValues() ? "" : "(" + last() + ")"));
		if (exhaustively)
			System.out.println("\t values = {" + stringOfCurrentValues() + "}" + "\nStructures\n" + stringOfStructures());
	}

}
