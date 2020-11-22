/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package variables;

import java.util.stream.IntStream;

import sets.LinkedSetBinary;
import solver.Solver;

public final class DomainBinary extends LinkedSetBinary implements Domain {

	private Variable var;

	private Integer typeIdentifier;

	private Solver solver;

	private Boolean indexesMatchValues;

	private int firstValue, secondValue;

	@Override
	public final Variable var() {
		return var;
	}

	@Override
	public final int typeIdentifier() {
		return typeIdentifier != null ? typeIdentifier : (typeIdentifier = Domain.typeIdentifierFor(new int[] { firstValue, secondValue }));
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
	public final boolean indexesMatchValues() {
		return indexesMatchValues != null ? indexesMatchValues : (indexesMatchValues = IntStream.range(0, initSize()).noneMatch(a -> a != toVal(a)));
	}

	public DomainBinary(Variable var, int firstValue, int secondValue) {
		super(2);
		this.var = var;
		this.firstValue = firstValue;
		this.secondValue = secondValue;
	}

	@Override
	public int toIdx(int v) {
		return v == firstValue ? 0 : v == secondValue ? 1 : -1;
	}

	@Override
	public int toVal(int a) {
		assert a == 0 || a == 1;
		return a == 0 ? firstValue : secondValue;
	}

	@Override
	public Object allValues() {
		return new int[] { firstValue, secondValue };
	}

	@Override
	public String toString() {
		return "dom(" + var().id() + ")";
	}

}
