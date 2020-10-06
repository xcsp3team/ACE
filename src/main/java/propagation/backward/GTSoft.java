/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.backward;

import org.xcsp.common.Types.TypeFramework;

import constraints.Constraint;
import propagation.soft.LowerBoundCapability;
import search.Solver;
import utility.Kit;
import variables.Variable;

/**
 * The is a class for <i>generate and test</i>.
 */
public final class GTSoft extends PropagationBackward implements LowerBoundCapability {

	@Override
	public final long getLowerBound() {
		return Constraint.costOfCoveredConstraintsIn(solver.pb.constraints);
	}

	public GTSoft(Solver solver) {
		super(solver);
		Kit.control(pb().framework == TypeFramework.MAXCSP, () -> "MaxCSP is not indicated in your settings");
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		assert x.isAssigned();
		if (solver.futVars.size() == 0)
			return Constraint.costOfCoveredConstraintsIn(solver.pb.constraints) < solver.solManager.bestBound;
		return true;
	}
}
