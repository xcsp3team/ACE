/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.backward;

import java.util.stream.Stream;

import search.Solver;
import variables.Variable;

/**
 * The basic BT Algorithm.
 */
public final class BT extends PropagationBackward {

	public BT(Solver solver) {
		super(solver);
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		assert x.isAssigned();
		return Stream.of(solver.pb.constraints).allMatch(c -> c.ignored || c.futvars.size() > 0 || c.seekFirstSupport());
	}
}
