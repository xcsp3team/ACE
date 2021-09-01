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

import propagation.Propagation;

/**
 * EXPERIMENTAL (TO BE CONTINUED/FINISHED)
 * 
 * @author Christophe Lecoutre
 * 
 */
public final class DomainInfinite implements Domain {

	private Variable var;

	private Integer typeIdentifier;

	private Propagation propagation;

	private Integer assignedValue;

	private int assignedLevel;

	public final Variable var() {
		return var;
	}

	@Override
	public final int typeIdentifier() {
		return typeIdentifier != null ? typeIdentifier : (typeIdentifier = Domain.typeIdentifierFor(Integer.MIN_VALUE, Integer.MAX_VALUE));
		// should we be careful about avoiding confusion with other types of domains?
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
	public void setNumberOfLevels(int nLevels) {
	}

	public DomainInfinite(Variable var) {
		this.var = var;
	}

	@Override
	public final boolean indexesMatchValues() {
		return false; // ????
	}

	@Override
	public int toIdx(int v) {
		return 0; // ???
	}

	@Override
	public int toVal(int a) {
		return assignedValue == null ? 0 : assignedValue;
	}

	@Override
	public int initSize() {
		return 1; // Constants.VAL_PLUS_INFINITY_INT ???
	}

	@Override
	public int size() {
		int s = assignedValue == null ? 2 : 1; // removed ? 0 : 1; // Constants.VAL_PLUS_INFINITY_INT;
		return s;
	}

	@Override
	public boolean contains(int a) {
		return true; // assignedValue == null ? true : assignedValue == a;
	}

	@Override
	public int first() {
		// if (assignedValue != null)
		return 0; // assignedValue;
		// throw new UnreachableCodeException();
	}

	@Override
	public int next(int a) {
		throw new AssertionError();
	}

	@Override
	public int last() {
		throw new AssertionError();
	}

	@Override
	public int prev(int a) {
		throw new AssertionError();
	}

	@Override
	public int lastRemoved() {
		throw new AssertionError();
	}

	@Override
	public int prevRemoved(int a) {
		throw new AssertionError();
	}

	@Override
	public int lastRemovedLevel() {
		int res = assignedValue == null ? -1 : assignedLevel;
		return res;
	}

	@Override
	public int removedLevelOf(int a) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void remove(int a, int level) {
		throw new AssertionError();
	}

	@Override
	public int reduceTo(int a, int level) {
		// assert level >= 0 && assignedValue == null : level + " " + assignedValue;
		assignedValue = a;
		assignedLevel = level;
		return 1; // nbRemovals set to 1 in order to avoid overflow
	}

	@Override
	public void restoreBefore(int level) {
		// System.out.println("trying restoring " + var);
		if (assignedLevel >= level) {
			// System.out.println("restoring " + var);
			assignedLevel = -1;
			assignedValue = null;
			// removed = false;
		}
	}

	@Override
	public Object allValues() {
		throw new UnsupportedOperationException();
	}

	@Override
	public void setMark() {
		throw new AssertionError();

	}

	@Override
	public void setMark(int level) {
		throw new AssertionError();

	}

	@Override
	public void restoreAtMark() {
		throw new AssertionError();

	}

	@Override
	public void restoreAtMark(int level) {
		throw new AssertionError();

	}

	@Override
	public int getMark() {
		throw new AssertionError();
	}

	@Override
	public String toString() {
		return "dom(" + var() + ")";
	}

}
