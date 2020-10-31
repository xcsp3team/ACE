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

/**
 * A reviser is attached to a propagation technique and allows us to manage revisions (within a generic filtering scheme).
 */
public abstract class Reviser {

	/**
	 * The propagation technique to which the reviser is attached.
	 */
	protected PropagationForward propagation;

	/**
	 * The number of revisions, i.e., the number of calls to <code> revise(c,x) </code>
	 */
	public long nRevisions, nUselessRevisions;

	public Reviser(PropagationForward propagation) {
		this.propagation = propagation;
	}

	public abstract boolean mustBeAppliedTo(Constraint c, Variable x);

	public abstract void applyTo(Constraint c, Variable x);

	public final boolean revise(Constraint c, Variable x) {
		assert !x.isAssigned() && c.involves(x);
		if (mustBeAppliedTo(c, x)) {
			nRevisions++;
			int sizeBefore = x.dom.size();
			applyTo(c, x);
			int sizeAfter = x.dom.size();
			if (sizeBefore == sizeAfter)
				nUselessRevisions++;
			else if (!propagation.handleReduction(x, sizeAfter))
				return false;
		}
		return true;
	}

}
