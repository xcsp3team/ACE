/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.revisers;

import constraints.Constraint;
import propagation.Forward;
import variables.Domain;
import variables.Variable;

/**
 * Basic object to perform revisions, as in AC3
 */
public class Reviser1 extends Reviser {

	public Reviser1(Forward propagation) {
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
