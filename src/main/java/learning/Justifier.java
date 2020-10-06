/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package learning;

import constraints.Constraint;
import interfaces.ObserverDomainReduction;
import search.Solver;
import utility.Enums.ELearningState;
import variables.Variable;
import variables.domains.Domain;

public final class Justifier implements ObserverDomainReduction {

	// private final LearnerStates learner;

	/**
	 * Stores which constraint is responsible of each value deletion. More precisely justifications[x][a] is either null or the constraint
	 * responsible for the deletion of the value with index a from the domain of the variable x
	 */
	public final Constraint[][] justifications;

	private final Solver solver; // redundant field

	public Justifier(LearnerStates learner) {
		// this.learner = learner;
		this.solver = learner.solver;
		if (solver.rs.cp.learning.state != ELearningState.NO) {
			Variable[] vars = learner.solver.pb.variables;
			this.justifications = new Constraint[vars.length][];
			for (int i = 0; i < justifications.length; i++) {
				Domain dom = vars[i].dom;
				this.justifications[i] = new Constraint[dom.initSize()];
				for (int idx = 0; idx < justifications[i].length; idx++)
					if (!dom.isPresent(idx))
						justifications[i][idx] = Constraint.TAG; // because values removed at construction time
			}
			solver.pb.observersDomainReduction.add(this);
		} else
			this.justifications = null;
	}

	@Override
	public void actAfterRemoval(Variable x, int a) {
		justifications[x.num][a] = solver.depth() == 0 ? Constraint.TAG : solver.propagation.currFilteringCtr;
	}

	@Override
	public void actAfterRemovals(Variable x, int nbRemovals) {
		Constraint c = solver.depth() == 0 ? Constraint.TAG : solver.propagation.currFilteringCtr;
		for (int cnt = 0, a = x.dom.lastRemoved(); cnt < nbRemovals; cnt++, a = x.dom.prevRemoved(a))
			justifications[x.num][a] = c;
	}
}
