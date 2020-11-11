/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package variables.domains;

import org.xcsp.common.Constants;

import utility.Kit;
import variables.Variable;

public final class DomainHugeInfinite extends DomainHuge {
	private Integer assignedValue;

	private int assignedLevel;

	// private boolean removed;

	@Override
	public void finalizeConstruction(int nLevels) {}

	public DomainHugeInfinite(Variable var, int firstValue, int lastValue) {
		super(var, firstValue, lastValue);
		Kit.control(firstValue == Constants.MINUS_INFINITY_INT && lastValue == Constants.PLUS_INFINITY_INT);
	}

	@Override
	public final boolean indexesMatchValues() {
		return false;
	}

	@Override
	public int toIdx(int v) {
		return 0;
		// throw new UnreachableCodeException();
		// return v;
	}

	@Override
	public int toVal(int a) {
		return assignedValue == null ? 0 : assignedValue;
		// throw new UnreachableCodeException();
		// return a;
	}

	@Override
	public int initSize() {
		return 1; // Constants.VAL_PLUS_INFINITY_INT;
	}

	@Override
	public int size() {
		int s = assignedValue == null ? 2 : 1; // removed ? 0 : 1; // Constants.VAL_PLUS_INFINITY_INT;
		// System.out.println("asking " + var + " " + s);
		return s;
	}

	@Override
	public boolean isPresent(int a) {
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
		// if (assignedValue != null)
		// return assignedValue;
		throw new AssertionError();
	}

	@Override
	public int prev(int a) {
		throw new AssertionError();
	}

	@Override
	public int get(int i) {
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
		// System.out.println("lasrrem " + res);
		return res;
	}

	@Override
	public boolean isRemovedAtLevel(int a, int level) {
		throw new AssertionError();
	}

	@Override
	public int getRemovedLevelOf(int a) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void remove(int a, int level) {
		// Kit.control(a == assignedValue);
		// removed = true;
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

}
