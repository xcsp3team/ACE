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
 * The is a class for <i>generate and test</i>.
 */
public final class GT extends PropagationBackward {
	public GT(Solver solver) {
		super(solver);
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		assert x.isAssigned();
		return solver.futVars.size() > 0 || Stream.of(solver.pb.constraints).allMatch(c -> c.ignored || c.seekFirstSupport());
	}
}
