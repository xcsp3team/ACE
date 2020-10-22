/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package variables.domains;

import static org.xcsp.common.Types.TypeConditionOperatorSet.IN;
import static org.xcsp.common.Types.TypeConditionOperatorSet.NOTIN;
import static org.xcsp.common.Types.TypeOperatorRel.GE;
import static org.xcsp.common.Types.TypeOperatorRel.GT;
import static org.xcsp.common.Types.TypeOperatorRel.LE;
import static org.xcsp.common.Types.TypeOperatorRel.LT;
import static utility.Kit.control;
import static utility.Kit.log;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.stream.IntStream;

import org.xcsp.common.Range;
import org.xcsp.common.Types.TypeConditionOperatorSet;
import org.xcsp.common.Types.TypeOperatorRel;

import interfaces.ObserverDomainReduction;
import search.Solver;
import utility.Kit;
import utility.sets.LinkedSet;
import utility.sets.SetDense;
import variables.Variable;

public interface Domain extends LinkedSet {

	static final int TAG_RANGE = Integer.MAX_VALUE;
	static final int TAG_SYMBOLS = Integer.MAX_VALUE - 1;

	static boolean similarDomains(Domain[] doms1, Domain[] doms2) {
		return doms1.length == doms2.length && IntStream.range(0, doms1.length).allMatch(i -> doms1[i].typeIdentifier() == doms2[i].typeIdentifier());
	}

	static final List<int[]> domainTypes = new ArrayList<int[]>();

	static int typeIdentifierFor(int[] values) {
		int j = IntStream.range(0, domainTypes.size()).filter(i -> Arrays.equals(values, domainTypes.get(i))).findFirst().orElse(-1);
		if (j != -1)
			return j;
		domainTypes.add(values);
		return domainTypes.size() - 1;
	}

	public static void setMarks(Variable[] variables) {
		for (Variable x : variables)
			x.dom.setMark();
	}

	public static void restoreAtMarks(Variable[] variables) {
		for (Variable x : variables)
			x.dom.restoreAtMark();
	}

	public static void setMarks(Variable[] variables, int level) {
		for (Variable x : variables)
			x.dom.setMark(level);
	}

	public static void restoreAtMarks(Variable[] variables, int level) {
		for (Variable x : variables)
			x.dom.restoreAtMark(level);
	}

	default boolean areInitValuesExactly(Range range) {
		return initSize() == range.length() && IntStream.range(0, initSize()).allMatch(a -> toVal(a) == range.start + a);
	}

	default boolean areInitValuesSubsetOf(int[] values) {
		return initSize() <= values.length && IntStream.range(0, initSize()).allMatch(a -> Kit.isPresent(toVal(a), values));
	}

	/**
	 * Returns the variable to which the domain is attached.
	 * 
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
	 * Returns the solver behind the scene.
	 * 
	 * @return
	 */
	Solver solver();

	void setSolver(Solver solver);

	/**
	 * Indicates if indexes (of values) and values match, i.e. if for every index a, we have toVal(a) = a, and for every value v, we have toIdx(v)=v.
	 * 
	 * @return {@code true} iff indexes (of values) and values match
	 */
	boolean indexesMatchValues();

	default String typeName() {
		return "D" + typeIdentifier();
	}

	/**
	 * Returns the index of the specified value, or a negative integer if the specified value does not belong to the initial domain. No assumption is
	 * made about the fact that the specified value belongs or not to the current domain.
	 */
	int toIdx(int v);

	/** Returns the value at the specified index. */
	int toVal(int a);

	/** Returns the index of the specified value, but only if the value belongs to the current domain. Returns -1, otherwise. */
	default int toPresentIdx(int v) {
		int a = toIdx(v);
		return a < 0 || !isPresent(a) ? -1 : a;
	}

	/**
	 * Determines whether the specified value belongs to the current domain.
	 */
	default boolean isPresentValue(int v) {
		int a = toIdx(v);
		return a >= 0 && isPresent(a);
	}

	/**
	 * Returns true iff the domain has only one remaining value, whose index is specified.
	 */
	default boolean onlyContains(int a) {
		return size() == 1 && isPresent(a);
	}

	/**
	 * Returns true iff the domain has only one remaining value, the one that is specified.
	 */
	default boolean onlyContainsValue(int v) {
		return size() == 1 && v == toVal(first());
	}

	/**
	 * Returns the index of the unique value of the domain. This is similar to first(), but with an assert/control.
	 */
	default int unique() {
		assert size() == 1 : "Current size = " + size();
		return first();
	}

	/**
	 * Returns randomly the index of a current value in the domain.
	 */
	default int random() {
		return get(solver().rs.random.nextInt(size()));
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
	 * Returns the unique value of the domain. This is similar to firstValue(), but with an assert/control.
	 */
	default int uniqueValue() {
		return toVal(unique());
	}

	/**
	 * Determines if a value has been removed at the current depth of the (tree) solver.
	 */
	default boolean isModifiedAtCurrentDepth() {
		return lastRemovedLevel() == solver().depth();
	}

	default boolean is01() {
		return initSize() == 2 && toIdx(0) == 0 && toIdx(1) == 1;
	}

	default long highestValueDistance() {
		return Math.abs((long) firstValue() - lastValue());
	}

	/**********************************************************************************************
	 * Section about removals
	 *********************************************************************************************/

	default void executeOnValues(Consumer<Integer> consumer) {
		for (int a = first(); a != -1; a = next(a))
			consumer.accept(toVal(a));
	}

	/**
	 * Removes definitively the value at the specified index. <br />
	 * Important: this method must only called when building the problem.
	 */
	default void removeValueAtConstructionTime(int v) {
		control(var().pb.solver == null, () -> "Must be called before the solver being built.");
		remove(toIdx(v), 0);
		var().pb.nValuesRemoved++;
		var().pb.stuff.nValuesRemovedAtConstructionTime++;
	}

	default void reduceToValueAtConstructionTime(int v) {
		for (int a = first(); a != -1; a = next(a))
			if (toVal(a) != v)
				removeValueAtConstructionTime(toVal(a));
	}

	default boolean afterElementaryCalls(int sizeBefore) {
		return size() == sizeBefore ? true : size() == 0 ? fail() : solver().propagation.handleReductionSafely(var());
	}

	/**
	 * Removes the value at the specified index. <br />
	 * The value is assumed to be present, and the variable to which the domain is attached is assumed to be future. <br />
	 * Important: the management of this removal with respect to propagation is not handled.
	 */
	default void removeElementary(int a) {
		Variable x = var();
		int depth = solver().depth();
		assert !x.isAssigned() && isPresent(a) && lastRemovedLevel() <= depth : x + " " + x.isAssigned() + " " + isPresent(a) + " " + lastRemovedLevel() + " "
				+ depth;
		// log.info("removing " + x + "=" + toVal(a) + " (index " + a + ") by constraint " + solver().propagation.currFilteringCtr);

		if (depth != lastRemovedLevel())
			solver().pushVariable(x); // push must always be performed before domain reduction
		remove(a, depth);
		for (ObserverDomainReduction observer : x.pb.observersDomainReduction)
			observer.actAfterRemoval(x, a);
		x.pb.nValuesRemoved++;
	}

	/**
	 * Removes the value at the specified index. <br />
	 * The value is assumed to be present. <br />
	 * Returns false if an inconsistency is detected (because this is the index of the last value of the domain). <br />
	 * The management of this removal with respect to propagation is handled.
	 */
	default boolean remove(int a) {
		assert isPresent(a);
		if (size() == 1)
			return fail();
		removeElementary(a);
		return solver().propagation.handleReductionSafely(var());
	}

	/**
	 * Removes the value at the specified index, if present.<br />
	 * Returns false if an inconsistency is detected (because this is the index of the last value of the domain). <br />
	 * But if the index is not present, returns true (non aggressive mode). <br />
	 * The management of this removal with respect to propagation is handled.
	 */
	default boolean removeIfPresent(int a) {
		return !isPresent(a) || remove(a);
	}

	/**
	 * Removes the value at the specified index. <br />
	 * The value is assumed to be present. <br />
	 * When called, we have the guarantee that no inconsistency can be detected (because the value is present and the domain contains at least another
	 * value). <br />
	 * The management of this removal with respect to propagation is handled.
	 */
	default void removeSafely(int a) {
		assert isPresent(a) && size() > 1;
		removeElementary(a);
		solver().propagation.handleReductionSafely(var());
	}

	/**
	 * Removes the values (at the indexes) given by the specified array of flags. <br>
	 * When a flag is set to false, this means that the corresponding value must be removed. <br />
	 * Returns false if an inconsistency is detected. <br />
	 * The management of these removals with respect to propagation is handled.
	 */
	default boolean remove(boolean[] flags, int nRemovals) {
		assert 0 < nRemovals && nRemovals <= size() && flags.length == initSize()
				&& IntStream.range(0, initSize()).filter(a -> isPresent(a) && !flags[a]).count() == nRemovals;
		if (size() == nRemovals)
			return fail();
		for (int cnt = 0, a = first(); cnt < nRemovals; a = next(a))
			if (!flags[a]) {
				removeElementary(a);
				cnt++;
			}
		return solver().propagation.handleReductionSafely(var());
	}

	/**
	 * Removes the values at the indexes given in the specified set. <br />
	 * If the specified boolean is set to true, a test is performed to only consider values that are present in the current domain. <br />
	 * Returns false if an inconsistency is detected. <br />
	 * The management of these removals with respect to propagation is handled.
	 */
	default boolean remove(SetDense idxs, boolean testPresence) {
		if (testPresence) {
			if (size() == 1) {
				for (int i = idxs.limit; i >= 0; i--)
					if (isPresent(idxs.dense[i]))
						return fail();
				return true;
			}
			int sizeBefore = size();
			for (int i = idxs.limit; i >= 0; i--)
				if (isPresent(idxs.dense[i]))
					removeElementary(idxs.dense[i]);
			return afterElementaryCalls(sizeBefore);
		} else {
			assert IntStream.range(0, idxs.size()).allMatch(i -> isPresent(idxs.dense[i]));
			if (idxs.size() == 0)
				return true;
			if (size() == idxs.size())
				return fail();
			for (int i = idxs.limit; i >= 0; i--)
				removeElementary(idxs.dense[i]);
			return solver().propagation.handleReductionSafely(var());
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
		assert isPresent(a) : a + " is not present";
		if (size() == 1)
			return 0; // 0 removal
		Variable x = var();
		int depth = solver().depth();

		if (lastRemovedLevel() != depth)
			solver().pushVariable(x); // push above must always be performed before domain reduction
		int nRemovals = reduceTo(a, depth);
		for (ObserverDomainReduction observer : x.pb.observersDomainReduction)
			observer.actAfterRemovals(x, nRemovals);
		x.pb.nValuesRemoved += nRemovals;
		assert nRemovals >= 0 && size() == 1 : "nRemovals: " + nRemovals + " size:" + size();
		return nRemovals;
	}

	/**
	 * Removes any value whose index is different from the specified index. <br />
	 * Returns false if an inconsistency is detected (domain wipe-out). <br />
	 * Important: the value at the specified index is not necessarily present in the domain. <br />
	 * In that case, it automatically returns false. <br />
	 * The management of this removal with respect to propagation is handled.
	 */
	default boolean reduceTo(int a) {
		return !isPresent(a) ? fail() : reduceToElementary(a) == 0 || solver().propagation.handleReductionSafely(var());
	}

	/**
	 * Removes the values that are different from the specified value. <br />
	 * Returns false if an inconsistency is detected (domain wipe-out). <br />
	 * Important: the specified value is not necessarily present in the domain. <br />
	 * The propagation queue is updated (if necessary).
	 */
	default boolean reduceToValue(int v) {
		int a = toPresentIdx(v);
		return a == -1 ? fail() : reduceToElementary(a) == 0 || solver().propagation.handleReductionSafely(var());
	}

	/**
	 * Forces failure through this domain.
	 */
	default boolean fail() {
		return solver().propagation.handleReduction(var(), 0);
	}

	/**
	 * Removes the specified value. <br />
	 * Important: the value is assumed to be present. <br />
	 * Returns false if an inconsistency is detected (domain wipe-out). <br />
	 * The management of this removal with respect to propagation is handled.
	 */
	default boolean removeValue(int v) {
		int a = toPresentIdx(v);
		assert a != -1;
		return remove(a);
	}

	/**
	 * Removes the specified value, if present. <br />
	 * If the value is not present, the method returns true (non aggressive mode). <br />
	 * Otherwise, returns false if an inconsistency is detected (domain wipe-out). <br />
	 * The management of this (possible) removal with respect to propagation is handled.
	 */
	default boolean removeValueIfPresent(int v) {
		int a = toPresentIdx(v);
		return a == -1 || remove(a);
	}

	/**
	 * Removes the values that satisfies the relational operation. <br />
	 * Returns false if an inconsistency is detected (domain wipe-out). <br />
	 * The management of these possible removals with respect to propagation is handled.
	 */
	default boolean removeValues(TypeOperatorRel type, int limit) {
		int sizeBefore = size();
		switch (type) {
		case LT:
			limit = limit != Integer.MIN_VALUE ? limit - 1 : limit;
		case LE:
			if (lastValue() <= limit)
				return fail();
			for (int a = first(); a != -1 && toVal(a) <= limit; a = next(a))
				removeElementary(a);
			break;
		case GT:
			limit = limit != Integer.MAX_VALUE ? limit + 1 : limit;
		case GE:
			if (firstValue() >= limit)
				return fail();
			for (int a = last(); a != -1 && toVal(a) >= limit; a = prev(a))
				removeElementary(a);
		}
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValues(TypeOperatorRel type, long limit) {
		return removeValues(type, limit <= Integer.MIN_VALUE ? Integer.MIN_VALUE : limit >= Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) limit);
	}

	default boolean removeValuesLessThan(long limit) {
		return removeValues(LT, limit);
	}

	default boolean removeValuesLessThanOrEqual(long limit) {
		return removeValues(LE, limit);
	}

	default boolean removeValuesGreaterThan(long limit) {
		return removeValues(GT, limit);
	}

	default boolean removeValuesGreaterThanOrEqual(long limit) {
		return removeValues(GE, limit);
	}

	default boolean removeValues(TypeOperatorRel type, long limit, int coeff) {
		// System.out.println("removing " + var());
		// System.out.println(var() + " " + type + " " + limit + " " + coeff);
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
		// System.out.println(var() + " " + type + " " + newLimit);
		return removeValues(type, newLimit);
	}

	default boolean removeValuesOld(TypeOperatorRel type, long limit, int coeff) {
		// OLD ALTERNATIVE: keep it the time to be sure that the code above is correct
		int sizeBefore = size();
		switch (type) {
		case LT:
			limit = limit != Long.MIN_VALUE ? limit - 1 : limit;
		case LE:
			if (size() == 1)
				return coeff * firstValue() <= limit ? fail() : true;
			if (coeff > 0)
				for (int a = first(); a != -1 && coeff * toVal(a) <= limit; a = next(a))
					removeElementary(a);
			else
				for (int a = last(); a != -1 && coeff * toVal(a) <= limit; a = prev(a))
					removeElementary(a);
			break;
		case GT:
			limit = limit != Long.MAX_VALUE ? limit + 1 : limit;
		case GE:
			if (size() == 1)
				return coeff * firstValue() >= limit ? fail() : true;
			if (coeff > 0)
				for (int a = last(); a != -1 && coeff * toVal(a) >= limit; a = prev(a)) {
					removeElementary(a);
				}
			else
				for (int a = first(); a != -1 && coeff * toVal(a) >= limit; a = next(a))
					removeElementary(a);
		}
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValues(TypeConditionOperatorSet type, Domain dom, int offset) {
		assert type != null;
		boolean present = type == IN;
		if (size() == 1)
			return dom.isPresentValue(firstValue() - offset) == present ? fail() : true;
		int sizeBefore = size();
		for (int a = first(); a != -1; a = next(a))
			if (dom.isPresentValue(toVal(a) - offset) == present)
				removeElementary(a);
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValues(TypeConditionOperatorSet type, Domain dom) {
		assert type != null;
		boolean present = type == IN;
		if (size() == 1)
			return dom.isPresentValue(firstValue()) == present ? fail() : true;
		int sizeBefore = size();
		for (int a = first(); a != -1; a = next(a))
			if (dom.isPresentValue(toVal(a)) == present)
				removeElementary(a);
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValuesIn(Domain dom) {
		return removeValues(IN, dom);
	}

	default boolean removeValuesNotIn(Domain dom) {
		return removeValues(NOTIN, dom);
	}

	default boolean removeValues(TypeConditionOperatorSet type, Set<Integer> set) {
		assert type != null;
		boolean present = type == IN;
		if (size() == 1)
			return set.contains(firstValue()) == present ? fail() : true;
		int sizeBefore = size();
		for (int a = first(); a != -1; a = next(a))
			if (set.contains(toVal(a)) == present)
				removeElementary(a);
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValuesIn(Set<Integer> set) {
		int sizeBefore = size();
		if (size() < set.size()) {
			for (int a = first(); a != -1; a = next(a))
				if (set.contains(toVal(a)))
					removeElementary(a);
		} else {
			for (int v : set)
				if (isPresentValue(v))
					removeElementary(toIdx(v));
		}
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValuesIn(SetDense set) {
		int sizeBefore = size();
		for (int i = set.limit; i >= 0; i--) {
			int v = set.dense[i];
			if (isPresentValue(v))
				removeElementary(toIdx(v));
		}
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValues(TypeConditionOperatorSet type, int start, int stop) {
		assert type != null;
		Kit.control(type == IN, () -> "NOTIN not currently implemented");
		int first = firstValue(), last = lastValue();
		int v = Math.max(start, first);
		int limit = Math.min(stop - 1, last);
		if (v == first && limit == last)
			return fail();
		while (!isPresentValue(v) && v <= limit)
			v++;
		if (v > limit)
			return true;
		int sizeBefore = size();
		for (int a = toIdx(v); a != -1; a = next(a)) {
			v = toVal(a);
			if (v > limit)
				break;
			removeValue(v);
		}
		return afterElementaryCalls(sizeBefore);
	}

	default boolean removeValuesInRange(int start, int stop) {
		return removeValues(IN, start, stop);
	}

	default boolean removeIndexesChecking(Predicate<Integer> p) {
		if (size() == 1)
			return p.test(first()) ? fail() : true;
		int sizeBefore = size();
		for (int a = first(); a != -1; a = next(a))
			if (p.test(a))
				removeElementary(a);
		return afterElementaryCalls(sizeBefore);
	}

	default boolean iterateStoppingWhen(Predicate<Integer> p) {
		for (int a = first(); a != -1; a = next(a))
			if (p.test(a))
				return true;
		return false;
	}

	default boolean iterateOnValuesStoppingWhen(Predicate<Integer> p) {
		for (int a = first(); a != -1; a = next(a))
			if (p.test(toVal(a)))
				return true;
		return false;
	}

	default boolean subsetOf(Domain dom) {
		for (int a = first(); a != -1; a = next(a))
			if (!dom.isPresentValue(toVal(a)))
				return false;
		return true;
	}

	default boolean overlapWith(Domain dom) {
		for (int a = first(); a != -1; a = next(a))
			if (dom.isPresentValue(toVal(a)))
				return true;
		return false;
	}

	/**********************************************************************************************
	 * Control and Display
	 *********************************************************************************************/

	/**
	 * Returns either an object Range or an array with all values of the initial domain
	 * 
	 * @return either an object Range or an array with all values of the initial domain
	 */
	Object allValues();

	default String prettyValueOf(int a) {
		return toVal(a) + "";
	}

	default String prettyAssignedValue() {
		return prettyValueOf(unique());
	}

	/**
	 * Displays a description of the domain. More information is displayed if the specified boolean is {@code true}
	 * 
	 * @param exhaustively
	 *            a boolean for getting more information
	 */
	default void display(boolean exhaustively) {
		log.fine("  Domain " + this + " (ivs=" + indexesMatchValues() + ", domainType=" + typeIdentifier() + ")");
		log.fine("\t initSize = " + initSize() + " and size = " + size());
		log.fine("\t first=" + first() + " and last=" + last());
		if (size() != 0)
			log.fine("\t first value = " + firstValue() + " and last value = " + lastValue());
		if (exhaustively)
			log.fine("\t values = {" + stringListOfValues() + "}" + "\nStructures\n" + stringOfStructures());
	}

	/**
	 * Returns a string denoting the list of the (current) values of the domain. Note that intervals are used when appropriate.
	 * 
	 * @return a string denoting the list of values of the domain
	 */
	default String stringListOfValues() {
		if (size() == 0)
			return "";
		StringBuilder sb = new StringBuilder();
		int prevVal = firstValue(), startInterval = prevVal;
		for (int a = next(first()); a != -1; a = next(a)) {
			int currVal = toVal(a);
			if (currVal != prevVal + 1) {
				sb.append(prevVal == startInterval ? prevVal : startInterval + (prevVal == startInterval + 1 ? " " : "..") + prevVal).append(" ");
				// when only two values, no need for an interval
				startInterval = currVal;
			}
			prevVal = currVal;
		}
		return sb.append(prevVal == startInterval ? prevVal : startInterval + (prevVal == startInterval + 1 ? " " : "..") + prevVal).toString();
	}

}

// /**
// * Removes the specified value, if present. <br />
// * If the value is not present, the method either returns false by failing (aggressive mode) or true (non aggressive mode). <br />
// * Otherwise, returns false if an inconsistency is detected (domain wipe-out). <br />
// * The management of this (possible) removal with respect to propagation is handled.
// */
// default boolean removeValue(int v, boolean agressive) {
// int a = toPresentIdx(v);
// return a != -1 ? remove(a) : !agressive || fail();
// }

/// **
// * Notify (to propagation process) that the domain has just been reduced (without any domain wipe-out).
// */
// default void notifyReduction() {
// assert size() > 0;
// solver().propagation.handleReductionSafely(var());
// }

// default boolean afterElementaryCalls() {
// return size() == 0 ? fail() : solver().propagation.handleReductionSafely(var());
// }

/// **
// * Removes the value at the specified index, if present.<br />
// * If the value is not present, either returns false (detected inconsistency) if the aggressive mode is activated, or true. <br />
// * The management of this removal with respect to propagation is handled.
// */
// default boolean remove(int a, boolean aggressive) {
// return isPresent(a) ? remove(a) : !aggressive || fail();
// }
// default boolean removeValsGT(long limit, int coeff) {
// if (var.isAssigned())
// return coeff * uniqueVal() > limit ? fail() : true;
// int sizeBefore = size();
// if (coeff > 0)
// for (int a = set.last(); a != -1 && coeff * toVal(a) > limit; a = set.prev(a))
// removeIdxElementary(a);
// else
// for (int a = set.first(); a != -1 && coeff * toVal(a) > limit; a = set.next(a))
// removeIdxElementary(a);
// return afterElementaryCalls(sizeBefore);
// }

// default boolean removeValsLT(long limit, int coeff) {
// if (var.isAssigned())
// return coeff * uniqueVal() < limit ? fail() : true;
// int sizeBefore = size();
// assert coeff != 0;
// if (coeff > 0)
// for (int a = set.first(); a != -1 && coeff * toVal(a) < limit; a = set.next(a))
// removeIdxElementary(a);
// else
// for (int a = set.last(); a != -1 && coeff * toVal(a) < limit; a = set.prev(a))
// removeIdxElementary(a);
// return afterElementaryCalls(sizeBefore);
// }
