/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.structures.forSac;

import constraints.Constraint;
import constraints.extension.CtrExtension;
import propagation.order1.singleton.SACSharing;
import variables.Variable;
import variables.domains.Domain;

/**
 * Basic form of inference.
 */
public class Inferrer1 extends Inferrer {

	private final int[] tuple;

	public Inferrer1(SACSharing sac) {
		super(sac);
		tuple = enforceSPAC ? new int[2] : null; // note that spac means here conservative dual consistency
	}

	@Override
	public boolean exploitInferences(Variable x, int a) {
		assert sac.queue.isEmpty();
		sac.queue.add(x);
		return true;
	}

	@Override
	public void updateInferences(Variable x, int a) {
		if (!enforceSPAC || sac.solver.depth() != 1)
			return;
		for (Constraint c : x.ctrs) {
			if (c.scp.length != 2 || !(c instanceof CtrExtension))
				continue;
			int p = c.positionOf(x);
			tuple[p] = a;
			int q = p == 0 ? 1 : 0;
			Domain dom = c.scp[q].dom;
			for (int b = dom.lastRemoved(); b != -1; b = dom.prevRemoved(b)) {
				if (dom.isRemovedAtLevel(b, 1)) {
					tuple[q] = b;
					((CtrExtension) c).removeTuple(tuple);
				}
			}
		}
	}

	@Override
	public void removeInferences() { // Nothing to do
	}
}
