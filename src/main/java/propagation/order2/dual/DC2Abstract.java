/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order2.dual;

import constraints.Constraint;
import propagation.PropagationQueue;
import search.Solver;
import variables.Variable;

public abstract class DC2Abstract extends DCAbstract {

	protected int[] stamp; // 1D = variable id

	private PropagationQueue queue;

	public DC2Abstract(Solver solver) {
		super(solver);
		this.stamp = new int[solver.pb.variables.length];
		this.queue = super.queue;
	}

	@Override
	protected final void actAfterFirstPropagationStep() {
		Variable[] variables = solver.pb.variables;
		if (time > variables.length) {
			int lastCheck = time - variables.length;
			for (int i = 0; i < queue.size();) {
				Variable var = queue.var(i);
				if (stamp[var.num] <= lastCheck || isMarkLastDropped(var.dom))
					queue.remove(var.num);
				else
					i++;
			}
			// queue.clear();
			// int id = solver.getVariableManager().getLastPastVariable().getId();
			// for (int i = 0; i < variables.length; i++)
			// if (i != id && stamp[i] > lastCheck && !variables[i].domain.getElements().isMarkLastDropped())
			// queue.add(variables[i]);

			// if (size != queue.size()) System.out.println("bef=" + size + " " + " aft=" +
			// queue.size() + " n=" + variables.length);
		}
		super.actAfterFirstPropagationStep();
	}

	@Override
	protected final boolean removeTuplesFrom(Variable x, int a, Constraint c) {
		boolean effective = super.removeTuplesFrom(x, a, c);
		if (effective)
			stamp[Variable.firstDifferentVariableIn(c.scp, x).num] = time;
		return effective;
	}

	@Override
	protected final int performSingletonTest(Variable x, int a) {
		if (time > solver.pb.variables.length)
			solver.setDomainsMarks(); // not a problem even if futureVariable is not assigned yet
		return super.performSingletonTest(x, a);
	}

	@Override
	protected final void updateStructures(Variable uniqueModifiedVariable) {
		if (uniqueModifiedVariable == null)
			for (Variable x : solver.pb.variables)
				stamp[x.num] = time;
		else
			stamp[uniqueModifiedVariable.num] = time;
	}
}

// Constraint[] constraints = futureVariable.ctrs;
// for (int i = 0; consistent && i < constraints.length; i++) {
// if (constraints[i].getArity() != 2)
// continue;
// Variable brotherVariable = constraints[i].getFirstVariableDifferentFrom(futureVariable);
// revisionManager.revise(constraints[i], brotherVariable);
// if (brotherVariable.domain.getCurrentSize() == 0)
// consistent = false;
// }
// if (consistent) {
// int id = futureVariable.id;
// int lastCheck = time - variables.length;
// for (int i = 0; i < variables.length; i++) {
// if (i == id || stamp[i] <= lastCheck)
// continue;
// Elements elements = variables[i].domain.getElements();
// // if (elements.getIndexAtMark() == elements.getLastDropped())
// // continue;
// ((QueueOfVariables) queue).add(variables[i]);
// }
//
// for (int i = 0; i < variables.length; i++)
// variables[i].domain.getElements().setMark();
// consistent = runPropagation();
