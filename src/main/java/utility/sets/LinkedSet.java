/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package utility.sets;

import java.util.function.Consumer;

/**
 * This class allows representing a list of elements perceived as indexes, i.e., elements whose values range from 0 to a specified capacity -1. For
 * instance, if the initial size (capacity) of the object is 10, then the list of indexes/elements is 0, 1, 2... , 9. One can remove elements of the
 * list. Then, one can iterate, in a forward way, currently present elements by using the methods <code> getFirst </code> and <code> getNext </code>.
 * Also, one can iterate, in a backward way, currently present elements by using the methods <code> getLast </code> and <code> getPrev </code>.
 * Initially, the set is full. On can iterate over deleted elements by using the methods <code> getLastDel </code> and <code> getPrevDel </code>. Each
 * deleted elements has an associated level that can be obtained by using the method getDelLevelFor. This kind of object is used for managing the
 * indexes of values of variable domains.
 */
public interface LinkedSet {

	void finalizeConstruction(int nLevels);

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
	boolean isPresent(int a);

	/**
	 * Returns the first present element (index of value) of the set, or -1 if the set is empty.
	 * 
	 * @return the first element of the current set
	 */
	int first();

	/**
	 * Returns the element (index of value) of the current set that comes after the specified one, or -1 if there is none.
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
	 * Returns the element (index of value) of the current set that comes before the specified one, or -1 if there is none.
	 * 
	 * @param a
	 *            the index of a value
	 * @return the element that comes before the specified one, or -1
	 */
	int prev(int a);

	/**
	 * Returns the ith element (index of value) of the current set. Be careful: with most of the implementations, this operation is not O(1).
	 * 
	 * @param i
	 *            the position of an element
	 * @return the ith element of the current set
	 */
	int get(int i);

	/**
	 * Returns the last removed element (index of value) of the set, or -1 if there is none.
	 * 
	 * @return the last removed element of the set
	 */
	abstract int lastRemoved();

	/**
	 * Returns the element (index of value) of the set that has been removed before the specified one, or -1 if there is none.
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
	 * Returns {@code true} iff the specified element (index of value) has been removed at the specified level.
	 * 
	 * @param a
	 *            the index of a value
	 * @param level
	 *            a level in search
	 * @return {@code true} iff the specified element has been removed at the specified level
	 */
	boolean isRemovedAtLevel(int a, int level);

	/**
	 * Returns the level of the specified removed element (index of value)
	 * 
	 * @param a
	 *            the index of a value
	 * @return the level of the specified removed element
	 */
	int getRemovedLevelOf(int a);

	/**
	 * Removes the specified element (index of value) at the specified level. The value is assumed to be currently present. BE CAREFUL: this method
	 * should normally not be called directly.
	 * 
	 * @param a
	 *            the index of a value
	 * @param level
	 *            a level in search
	 */
	void remove(int a, int level);

	/**
	 * Reduces the set to the specified element (index of value) at the specified level. BE CAREFUL: this method should normally not be called
	 * directly.
	 * 
	 * @param a
	 *            the index of a value
	 * @param level
	 *            a level in search
	 * @return the number of elements that are removed by this operation
	 */
	int reduceTo(int a, int level);

	/**
	 * Restores the structures at the state before the specified level.
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
	int indexAtMark();

	default void execute(Consumer<Integer> consumer, boolean reverse) {
		if (reverse)
			for (int a = last(); a != -1; a = prev(a))
				consumer.accept(a);
		else
			for (int a = first(); a != -1; a = next(a))
				consumer.accept(a);
	}

	default void execute(Consumer<Integer> consumer) {
		execute(consumer, false);
	}

	default void executeOnRemoved(Consumer<Integer> consumer) {
		for (int a = lastRemoved(); a != -1; a = prevRemoved(a))
			consumer.accept(a);
	}

	/**
	 * Returns the state of the object under the form of a sequence of bits. In other words, returns a binary representation corresponding to the
	 * present/deleted elements. If the ith bit of the jth long of the returned array is 1, it means that the (j*64)+ith value is currently present in
	 * the set. When not defined, null is returned.
	 * 
	 * @return the binary representation of the set
	 */
	long[] binaryRepresentation();

	/**
	 * Returns an array with all elements (indexes) from the current set. This method should not be called at the heart of the solving process, for
	 * efficiency reasons.
	 * 
	 * @return an array with all elements (indexes) of the current set
	 */
	int[] indexes();

	/**
	 * Returns {@code true} if the data structures seem to be valid.
	 * 
	 * @return {@code true} if the data structures look valid
	 */
	boolean controlStructures();

	default String stringOfDels(int size) {
		StringBuilder sb = new StringBuilder().append(size + "Dels :");
		for (int a = lastRemoved(), cnt = size - 1; cnt >= 0; a = prevRemoved(a))
			sb.append(' ').append(a);
		return sb.toString();
	}

	/**
	 * Returns a string showing the state of the main data structures.
	 * 
	 * @return a string showing the state of the main data structures
	 */
	default String stringOfStructures() {
		StringBuilder sb = new StringBuilder().append("Size=" + size() + " nRems=" + nRemoved() + "\nForward :");
		execute(a -> sb.append(' ').append(a));
		sb.append("\nBackward :");
		execute(a -> sb.append(' ').append(a), true);
		sb.append("\nDeleted :");
		executeOnRemoved(a -> sb.append(' ').append(a));
		return sb.toString();
	}

}
