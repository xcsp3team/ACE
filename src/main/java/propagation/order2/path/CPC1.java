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
package propagation.order2.path;

import constraints.Constraint;
import problem.cliques.CliqueManager;
import propagation.order2.SecondOrderConsistency;
import search.Solver;
import variables.domains.Domain;

public class CPC1 extends SecondOrderConsistency {
	protected CliqueManager cliqueManager;

	protected int[] nSupports;

	private boolean modified;

	public CPC1(Solver solver) {
		super(solver);
		cliqueManager = new CliqueManager(solver.pb);
		nSupports = new int[solver.pb.constraints.length];
	}

	private boolean filterConstraint(Constraint c) {
		Domain dom0 = c.scp[0].dom, dom1 = c.scp[1].dom;
		int sizeBefore0 = dom0.size(), sizeBefore1 = dom1.size();
		int[] tuple = c.tupleManager.localTuple;
		for (boolean foundSupport = c.seekFirstSupport(); foundSupport; foundSupport = c.seekNextSupport()) {
			if (!cliqueManager.isPathConsistent(c, tuple)) {
				modified = true;
				c.removeTuple(tuple);
				if (variant > 1) {
					if (!c.findArcSupportFor(0, tuple[0])) {
						dom0.removeElementary(tuple[0]);
						if (dom0.size() == 0)
							return false;
					}
					if (!c.findArcSupportFor(1, tuple[1])) {
						dom1.removeElementary(tuple[1]);
						if (dom1.size() == 0)
							return false;
					}
				}
			}
		}
		if (variant > 1) {
			assert queue.isEmpty();
			if (sizeBefore0 != dom0.size())
				queue.add(c.scp[0]);
			if (sizeBefore1 != dom1.size())
				queue.add(c.scp[1]);
			return propagate();
		}
		return true;
	}

	public boolean establishOnePass() {
		for (Constraint c : hards)
			if (c.scp.length == 2 && filterConstraint(c) == false)
				return false;
		return true;
	}

	@Override
	public boolean enforceSecondOrderConsistency() {
		do {
			modified = false;
			if (establishOnePass() == false)
				return false;
			System.out.println(" CPC : " + nTuplesRemoved + " tuples removed " + pb().nValuesRemoved + " values removed");
		} while (modified);
		return true;
	}
}
