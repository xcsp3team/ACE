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

public final class BTSoft extends PropagationBackward implements LowerBoundCapability {

	@Override
	public final long getLowerBound() {
		return Constraint.costOfCoveredConstraintsIn(solver.pb.constraints);
	}

	public BTSoft(Solver solver) {
		super(solver);
		Kit.control(solver.pb.settings.framework == TypeFramework.MAXCSP, () -> "MaxCSP is not indicated in your settings");
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		return Constraint.costOfCoveredConstraintsIn(solver.pb.constraints) < solver.solManager.bestBound;
	}

}
