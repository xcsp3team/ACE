/**
 *  AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 *  All rights reserved. 
 *  
 *  This program and the accompanying materials are made 
 *  available under the terms of the CONTRAT DE LICENCE 
 *  DE LOGICIEL LIBRE CeCILL which accompanies this distribution, 
 *  and is available at http://www.cecill.info
 */
package propagation.order2;

import interfaces.TagBinaryRelationFiltering;
import propagation.order1.AC;
import search.Solver;
import utility.Kit;

public abstract class SecondOrderConsistency extends AC implements TagBinaryRelationFiltering {

	protected int variant;

	public SecondOrderConsistency(Solver solver) {
		super(solver);
		solver.pb.stuff.cloneStructuresOfConstraintsWithArity(2, false);
		variant = cp().settingPropagation.variant;
		// TODO control the fact that we do not use SupportUnitRmbo as residues can become incorrect when tuples are removed
		Kit.control(!cp().settingProblem.shareBitVectors);
	}

	public abstract boolean enforceSecondOrderConsistency();

	@Override
	public boolean runInitially() {
		assert !solver.pb.stuff.hasSharedExtensionStructures() && !solver.pb.stuff.hasSharedConflictsStructures();
		if (variant > 0) {
			boolean consistent = super.runInitially();
			Kit.log.info("after AC, nbValuesRemoved=" + pb().nValuesRemoved);
			if (!consistent)
				return false;
		}
		return enforceSecondOrderConsistency();
	}
}
