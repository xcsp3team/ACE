/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension.structures;

import java.util.ArrayList;
import java.util.List;

import constraints.Constraint;
import interfaces.RegisteringCtrs;
import utility.exceptions.UnreachableCodeException;

public abstract class ExtensionStructure implements RegisteringCtrs {

	public final List<Constraint> registeredCtrs = new ArrayList<>();

	@Override
	public List<Constraint> registeredCtrs() {
		return registeredCtrs;
	}

	public ExtensionStructure(Constraint c) {
		registeredCtrs.add(c);
	}

	/**
	 * We assume that the given array corresponds to a tuple of indexes (and not to a tuple of values).
	 */
	public boolean removeTuple(int[] tupleToBeRemoved) {
		throw new UnreachableCodeException();
	}

	protected final void incrementNbTuplesRemoved() {
		firstRegisteredCtr().pb.solver.propagation.nTuplesRemoved++;
	}

}