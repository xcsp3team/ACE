/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package variables.domains;

import search.Solver;
import variables.Variable;

// EXPERIMENTAL (TO BE FINISHED) !!!!!!!!!!!!!!!!!!!!!!!!!!!
public final class DomainInfinite implements Domain {

	protected Variable var;

	public final Variable var() {
		return var;
	}

	protected Integer typeIdentifier;

	public final int typeIdentifier() {
		return typeIdentifier != null ? typeIdentifier : (typeIdentifier = Domain.typeIdentifierFor(new int[] { Integer.MIN_VALUE, Integer.MAX_VALUE }));
		// should we be careful about avoiding confusion with other types of domains?
	}

	protected Solver solver;

	@Override
	public final Solver solver() {
		return solver;
	}

	@Override
	public final void setSolver(Solver solver) {
		this.solver = solver;
	}

	private Integer assignedValue;

	private int assignedLevel;

	@Override
	public void finalizeConstruction(int nLevels) {
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
	public int indexAtMark() {
		throw new AssertionError();
	}

	@Override
	public long[] binaryRepresentation() {
		throw new AssertionError();
	}

	@Override
	public int[] indexes() {
		throw new AssertionError();
	}

	@Override
	public boolean controlStructures() {
		return true;
	}

	@Override
	public String toString() {
		return "dom(" + var().id() + ")";
	}

}
