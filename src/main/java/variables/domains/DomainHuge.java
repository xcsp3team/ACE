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
import utility.exceptions.UnreachableCodeException;
import variables.Variable;

public abstract class DomainHuge implements Domain {

	protected Variable var;

	protected Integer typeIdentifier;

	protected Solver solver;

	protected int firstValue, lastValue;

	@Override
	public final Variable var() {
		return var;
	}

	@Override
	public final int typeIdentifier() {
		return typeIdentifier != null ? typeIdentifier : (typeIdentifier = typeIdentifierFor(new int[] { -1, -1, firstValue, lastValue }));
		// -1 -1for avoiding confusion with other types of domains
	}

	@Override
	public final Solver solver() {
		return solver;
	}

	@Override
	public final void setSolver(Solver solver) {
		this.solver = solver;
	}

	@Override
	public boolean indexesMatchValues() {
		return firstValue == 0;
	}

	public DomainHuge(Variable var, int firstValue, int lastValue) {
		this.var = var;
		this.firstValue = firstValue;
		this.lastValue = lastValue;
	}

	@Override
	public int toIdx(int v) {
		return v - firstValue;
	}

	@Override
	public int toVal(int a) {
		return a + firstValue;
	}

	@Override
	public int initSize() {
		return lastValue - firstValue + 1;
	}

	@Override
	public void setMark() {
		throw new UnreachableCodeException();

	}

	@Override
	public void setMark(int level) {
		throw new UnreachableCodeException();

	}

	@Override
	public void restoreAtMark() {
		throw new UnreachableCodeException();

	}

	@Override
	public void restoreAtMark(int level) {
		throw new UnreachableCodeException();

	}

	@Override
	public int indexAtMark() {
		throw new UnreachableCodeException();
	}

	@Override
	public long[] binaryRepresentation() {
		throw new UnreachableCodeException();
	}

	@Override
	public int[] indexes() {
		throw new UnreachableCodeException();
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
