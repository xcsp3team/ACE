/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints;

import java.util.function.Consumer;
import java.util.function.Predicate;

import variables.Variable;
import variables.domains.Domain;

public final class TupleManager {

	/**
	 * The domains on which tuples will be iterated over.
	 */
	private final Domain[] doms;

	/**
	 * The arity. <br>
	 * Redundant field used for efficiency.
	 */
	private final int arity;

	/**
	 * Local tuple built and used by the object.
	 */
	public final int[] localTuple;

	/**
	 * Indicates which values must be kept fixed.
	 */
	private final boolean[] fixed;

	/**
	 * The tuple used by the assistant. It can be the local tuple or an external tuple (avoids bidirectional copy during search of support).
	 */
	public int[] currTuple;

	public TupleManager(Domain[] doms) {
		this.doms = doms;
		this.arity = doms.length;
		this.localTuple = new int[arity];
		this.fixed = new boolean[arity];
	}

	public TupleManager(Variable[] vars) {
		this(Variable.buildDomainsArrayFor(vars));
	}

	private boolean isValidCurrTuple() {
		for (int i = currTuple.length - 1; i >= 0; i--)
			if (!doms[i].isPresent(currTuple[i]))
				return false;
		return true;
	}

	public int nFixed() {
		int cnt = 0;
		for (int i = fixed.length - 1; i >= 0; i--)
			if (fixed[i])
				cnt++;
		return cnt;
	}

	/**
	 * Sets the given index (of a value) fixed.
	 */
	private void fix(int x, int a) {
		assert doms[x].isPresent(a) : a + " no more in " + doms[x];
		currTuple[x] = a;
		fixed[x] = true;
	}

	/**
	 * Puts in the specified array the first valid tuple. The specified array becomes the current tuple.
	 */
	public int[] firstValidTuple(int[] buffer) {
		this.currTuple = buffer;
		for (int i = buffer.length - 1; i >= 0; i--) {
			buffer[i] = doms[i].first();
			fixed[i] = false;
		}
		return buffer;
	}

	public int[] firstValidTuple() {
		return firstValidTuple(localTuple);
	}

	public int[] firstValidTupleWith(int x, int a, int[] buffer) {
		firstValidTuple(buffer);
		fix(x, a);
		return buffer;
	}

	public int[] firstValidTupleWith(int x, int a) {
		return firstValidTupleWith(x, a, localTuple);
	}

	public int[] firstValidTupleWith(int x, int a, int y, int b, int[] buffer) {
		firstValidTuple(buffer);
		fix(x, a);
		fix(y, b);
		return buffer;
	}

	public int[] firstValidTupleWith(int x, int a, int y, int b) {
		return firstValidTupleWith(x, a, y, b, localTuple);
	}

	/**
	 * Sets the first available tuple greater than the current one from the given frontier.
	 * 
	 * @param frontier
	 *            modifications of the current tuple are only allowed from frontier (included) to 0
	 * @return the position of the last modified index (the closest to 0), or <code> -1 </code> if there is no more available tuple
	 */
	private int setNextValidTupleBefore(int frontier) {
		for (int i = frontier; i >= 0; i--) {
			if (fixed[i])
				continue;
			int a = doms[i].next(currTuple[i]);
			if (a != -1) {
				currTuple[i] = a;
				return i;
			} else
				currTuple[i] = doms[i].first();
		}
		return -1;
	}

	/**
	 * Sets the first available valid tuple strictly greater than the current one, which is assumed to be valid.
	 * 
	 * @return the position (the closest to 0) of the last modified index, or <code> -1 </code> if there is no more available tuple
	 */
	public final int nextValidTuple() {
		assert isValidCurrTuple();
		return setNextValidTupleBefore(arity - 1);
	}

	/**
	 * Sets the first available tuple strictly greater than the current one, which is not assumed to be necessarily valid (hence, the term 'cautiously').
	 * 
	 * @return the position (the closest to 0) of the last modified index, or <code> -1 </code> if there is no more available tuple
	 */
	public final int nextValidTupleCautiously() {
		for (int i = 0; i < arity; i++)
			if (!doms[i].isPresent(currTuple[i])) { // i is the position (the closest to 0) of the first invalid index
				int modifiedPosition = setNextValidTupleBefore(i);
				if (modifiedPosition == -1)
					return -1;
				for (int j = i + 1; j < arity; j++)
					if (!fixed[j])
						currTuple[j] = doms[j].first();
				return modifiedPosition;
			}
		return nextValidTuple();
	}

	public final void overValidTuples(Consumer<int[]> p) {
		assert isValidCurrTuple();
		do {
			p.accept(currTuple);
		} while (nextValidTuple() != -1);
	}

	public final boolean findValidTupleSuchThat(Predicate<int[]> p) {
		assert isValidCurrTuple();
		do {
			if (p.test(currTuple))
				return true;
		} while (nextValidTuple() != -1);
		return false;
	}

	public final long countValidTuplesSuchThat(Predicate<int[]> p) {
		assert isValidCurrTuple();
		long cnt = 0;
		do {
			if (p.test(currTuple))
				cnt++;
		} while (nextValidTuple() != -1);
		return cnt;
	}

}