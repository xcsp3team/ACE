/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.structures.revisers;

import constraints.Constraint;
import propagation.order1.PropagationForward;
import variables.Variable;
import variables.domains.Domain;

/**
 * Object used to perform revisions, exploiting pre-computed number of conflicts.
 */
public class Reviser2 extends Reviser1 {

	public Reviser2(PropagationForward propagation) {
		super(propagation);
	}

	@Override
	public boolean mustBeAppliedTo(Constraint c, Variable x) {
		if (c.conflictsStructure == null)
			return true;
		int px = c.positionOf(x);
		return c.conflictsStructure.nMaxConflicts()[px] >= Variable.nValidTuplesBoundedAtMaxValueFor(c.scp, px);
	}

	@Override
	public void applyTo(Constraint c, Variable x) {
		if (c.conflictsStructure == null)
			super.applyTo(c, x);
		else {
			int px = c.positionOf(x);
			long nbValids = Variable.nValidTuplesBoundedAtMaxValueFor(c.scp, px);
			int[] nbConflicts = c.conflictsStructure.nConflicts()[px];
			Domain dom = x.dom;
			for (int a = dom.first(); a != -1; a = dom.next(a))
				if (nbConflicts[a] >= nbValids && !c.findArcSupportFor(px, a))
					x.dom.removeElementary(a);
		}
	}
}
