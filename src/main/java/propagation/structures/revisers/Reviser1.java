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
 * Basic object to perform revisions, as in AC3
 */
public class Reviser1 extends Reviser {

	public Reviser1(PropagationForward propagation) {
		super(propagation);
	}

	@Override
	public boolean mustBeAppliedTo(Constraint c, Variable x) {
		return true;
	}

	@Override
	public void applyTo(Constraint c, Variable x) {
		int px = c.positionOf(x);
		Domain dom = x.dom;
		for (int a = dom.first(); a != -1; a = dom.next(a)) {
			if (!c.findArcSupportFor(px, a))
				x.dom.removeElementary(a);
		}
	}
}
