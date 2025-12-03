/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package sets;

import java.util.function.Consumer;

/**
 * This interface allows representing a list of elements perceived as indexes, i.e., elements whose values range from 0
 * to a specified capacity -1. For instance, if the initial size (capacity) of the object is 10, then the list of
 * indexes/elements is 0, 1, 2... , 9. One can remove indexes of the list. Then, one can iterate, in a forward way,
 * currently present indexes by using the methods <code> first </code> and <code> next </code>. Also, one can iterate,
 * in a backward way, currently present indexes by using the methods <code> last </code> and <code> prev </code>.
 * Initially, the set is full. One can iterate over deleted indexes by using the methods <code> lastRemoved </code> and
 * <code> prevRemoved </code>. Each deleted index has an associated level that can be obtained by using the method
 * removedLevelOf. This kind of interface is notably used for managing the indexes of values of variable domains.
 * 
 * @author Christophe Lecoutre
 */
public interface SetLinked {

	/**
	 * Records the number of levels where elements can be removed. This is called when the information is available
	 * (e.g., when the problem has been built, and so, the number of variables is known).
	 * 
	 * @param nLevels
	 *            the number of levels where elements can be removed
	 */
	void setNumberOfLevels(int nLevels);

	/**
	 * Returns the initial size of the set, i.e., the number of elements initially present in the set.
	 * 
	 * @return the initial size of the set
	 */
	int initSize();

	/**
	 * Returns the current size of the set, i.e., the number of elements currently present in the set.
	 * 
	 * @return the current size of the set
	 */
	int size();

	/**
	 * Returns the number of elements currently removed from the set.
	 * 
	 * @return the number of removed elements
	 */
	default int nRemoved() {
		return initSize() - size();
	}

	/**
	 * Returns {@code true} iff the specified element (index of value) is present in the current set.
	 * 
	 * @param a
	 *            the index of a value
	 * @return {@code true} iff the specified element is present
	 */
	boolean contains(int a);

	/**
	 * Returns the first present element (index of value) of the set, or -1 if the set is empty.
	 * 
	 * @return the first element of the current set
	 */
	int first();

	/**
	 * Returns the element (index of value) of the current set that comes after the specified one, or -1 if there is
	 * none.
	 * 
	 * @param a
	 *            the index of a value
	 * @return the element that comes after the specified one, or -1
	 */
	int next(int a);

	/**
	 * Returns the last present element (index of value) of the set, or -1 if the set is empty.
	 * 
	 * @return the last element of the current set
	 */
	int last();

	/**
	 * Returns the element (index of value) of the current set that comes before the specified one, or -1 if there is
	 * none.
	 * 
	 * @param a
	 *            the index of a value
	 * @return the element that comes before the specified one, or -1
	 */
	int prev(int a);

	/**
	 * Returns the i+1th element of the set. BE CAREFUL: this operation is not in O(1), and so it only should be
	 * performed in very specific cases.
	 * 
	 * @param i
	 *            the position of the element in the set
	 */
	default int get(int i) {
		assert 0 <= i && i < size();
		if (i < size() / 2) {
			int a = first();
			for (int cnt = i - 1; cnt >= 0; cnt--)
				a = next(a);
			return a;
		}
		int a = last();
		for (int cnt = size() - i - 2; cnt >= 0; cnt--)
			a = prev(a);
		return a;
	}

	/**
	 * Returns the last removed element (index of value) of the set, or -1 if there is none.
	 * 
	 * @return the last removed element of the set
	 */
	abstract int lastRemoved();
	
	
	default boolean lastRemovedInsideBounds() {
		assert 0 < size();
		int a = lastRemoved();
		return first() < a && a < last();  // if a = -1, false is returned (since size() > 0)
	}
	

	/**
	 * Returns the element (index of value) of the set that has been removed before the specified one, or -1 if there is
	 * none.
	 * 
	 * @param a
	 *            the index of a value
	 * @return the element that has been removed before the specified one, or -1
	 */
	abstract int prevRemoved(int a);

	/**
	 * Returns the level of the last removed element, or -1 if no element was removed.
	 * 
	 * @return the level of the last removed element
	 */
	abstract int lastRemovedLevel();

	/**
	 * Returns the level of the specified removed element (index of value)
	 * 
	 * @param a
	 *            the index of a value
	 * @return the level of the specified removed element
	 */
	int removedLevelOf(int a);

	/**
	 * Removes the specified element (index of value) at the specified level. The value is assumed to be currently
	 * present. BE CAREFUL: this method should normally not be called directly.
	 * 
	 * @param a
	 *            the index of a value
	 * @param level
	 *            a level in search
	 */
	void remove(int a, int level);

	/**
	 * Reduces the set to the specified element (index of value) at the specified level. BE CAREFUL: this method should
	 * normally not be called directly.
	 * 
	 * @param a
	 *            the index of a value
	 * @param level
	 *            a level in search
	 * @return the number of elements that are removed by this operation
	 */
	int reduceTo(int a, int level);

	/**
	 * Restores the structure at the state before the specified level.
	 * 
	 * @param level
	 *            a level in search
	 */
	void restoreBefore(int level);

	/**
	 * Records a (simple) mark.
	 */
	void setMark();

	/**
	 * Records a mark for the specified level
	 * 
	 * @param level
	 *            a level in search
	 */
	void setMark(int level);

	/**
	 * Restores the set by using the current (simple) mark.
	 */
	void restoreAtMark();

	/**
	 * Restores the set by using the mark recorded at the specified level
	 * 
	 * @param level
	 *            a level in search
	 */
	void restoreAtMark(int level);

	/**
	 * Returns the element (index) identified by the current mark.
	 * 
	 * @return the element (index) identified by the current mark
	 */
	int getMark();

	/**
	 * Executes the specified function (consumer) for each present element (either forwardly, or backwardly depending on
	 * the specified boolean)
	 * 
	 * @param consumer
	 *            the function to be called for each present element
	 * @param reverse
	 *            if true, the elements are iterated in reverse order
	 */
	default void execute(Consumer<Integer> consumer, boolean reverse) {
		if (reverse)
			for (int a = last(); a != -1; a = prev(a))
				consumer.accept(a);
		else
			for (int a = first(); a != -1; a = next(a))
				consumer.accept(a);
	}

	/**
	 * Executes the specified function (consumer) for each present element (in a forward way, from the first element to
	 * the last one)
	 * 
	 * @param consumer
	 *            the function to be called for each present element
	 */
	default void execute(Consumer<Integer> consumer) {
		execute(consumer, false);
	}

	/**
	 * Returns the state of the object under the form of a sequence of bits. In other words, returns a binary
	 * representation corresponding to the present/deleted elements. If the ith bit of the jth long of the returned
	 * array is 1, it means that the (j*64)+ith value is currently present in the set. When not defined, null is
	 * returned.
	 * 
	 * @return the binary representation of the set, or null if not defined
	 */
	default long[] binary() {
		return null;
	}

	/**
	 * Returns {@code true} if the data structures seem to be valid.
	 * 
	 * @return {@code true} if the data structures look valid
	 */
	default boolean controlStructures() {
		return true;
	}

	/**
	 * @return a string showing the state of the main data structures
	 */
	default String stringOfStructures() {
		StringBuilder sb = new StringBuilder().append("Size=" + size() + " nRems=" + nRemoved() + "\nForward :");
		execute(a -> sb.append(' ').append(a));
		sb.append("\nBackward :");
		execute(a -> sb.append(' ').append(a), true);
		sb.append("\nDeleted :");
		for (int a = lastRemoved(); a != -1; a = prevRemoved(a))
			sb.append(' ').append(a);
		return sb.toString();
	}

}
