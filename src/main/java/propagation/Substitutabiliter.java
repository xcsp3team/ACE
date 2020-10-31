/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation;

import java.util.ArrayList;
import java.util.List;

import constraints.Constraint;
import problem.Problem;
import propagation.order1.PropagationForward;
import search.Solver;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public final class Substitutabiliter {
	protected Solver solver;

	private PropagationQueue queue;

	public Substitutabiliter(Solver solver) {
		this.solver = solver;
		this.queue = new PropagationQueue((PropagationForward) solver.propagation);
	}

	public boolean isSubstitutableBy(Constraint c, Variable x, int a, int b) {
		int p = c.positionOf(x);
		c.tupleManager.firstValidTupleWith(p, a);
		return !c.tupleManager.findValidTupleSuchThat(t -> {
			if (!c.checkIndexes(t))
				return false;
			t[p] = b;
			if (!c.checkIndexes(t))
				return true;
			t[p] = a;
			return false;
		});
	}

	public boolean isSubstitutableBy(Variable x, int a, int b) {
		for (Constraint c : x.ctrs)
			if (!isSubstitutableBy(c, x, a, b))
				return false;
		return true;
	}

	public boolean isSubstitutable(Variable x, int a) {
		Domain dom = x.dom;
		for (int b = dom.first(); b != -1; b = dom.next(b))
			if (b != a && isSubstitutableBy(x, a, b))
				return true;
		return false;
	}

	public int removeSubstitutableValuesOf(Variable x) {
		Domain dom = x.dom;
		int sizeBefore = dom.size();
		for (int a = dom.first(); a != -1; a = dom.next(a))
			if (isSubstitutable(x, a))
				x.dom.removeElementary(a);
		int nbRemovals = sizeBefore - dom.size();
		if (nbRemovals > 0)
			Kit.log.info(" => " + nbRemovals + " removals from " + x + " at level " + x.pb.solver.depth());
		return nbRemovals;
	}

	private void addFutureVariablesThatAreNeighboursOf(Variable x) {
		Variable[] neighbours = x.nghs;
		if (neighbours != null && neighbours.length <= solver.futVars.size()) {
			for (Variable y : neighbours)
				if (!y.isAssigned())
					queue.add(y);
		} else
			solver.futVars.execute(y -> {
				if (x != y && x.isNeighbourOf(y))
					queue.add(y);
			});
	}

	public final void removeSubstitutableValues() {
		queue.clear();
		solver.futVars.execute(x -> {
			if (removeSubstitutableValuesOf(x) > 0)
				addFutureVariablesThatAreNeighboursOf(x);
		});
		while (queue.size() > 0) {
			Variable x = queue.pickAndDelete(0);
			if (removeSubstitutableValuesOf(x) > 0)
				addFutureVariablesThatAreNeighboursOf(x);
		}
	}

	public int computeNbSubstitutableValuesOf(Variable x) {
		Domain dom = x.dom;
		int cnt = 0;
		for (int a = dom.first(); a != -1; a = dom.next(a))
			for (int b = dom.first(); b != -1; b = dom.next(b))
				if (b != a && isSubstitutableBy(x, a, b))
					cnt++;
		return cnt;
	}

	public double computeSubstitutabilityRatioOf(Problem problem) {
		double globalRatio = 0;
		for (Constraint c : problem.constraints) {
			double ratio = 0;
			for (Variable x : c.scp) {
				long size = computeNbSubstitutableValuesOf(x);
				ratio = ratio + size / (x.dom.size() * x.dom.size() - (double) x.dom.size());
			}
			globalRatio = globalRatio + (ratio / c.scp.length);
		}
		return globalRatio / problem.constraints.length;
	}

	public List<int[]> computeSubstitutabilityRelationOf(Variable x) {
		List<int[]> list = new ArrayList<>();
		Domain dom = x.dom;
		for (int a = dom.first(); a != -1; a = dom.next(a))
			for (int b = dom.first(); b != -1; b = dom.next(b))
				if (b != a && isSubstitutableBy(x, a, b))
					list.add(new int[] { a, b });
		return list;
	}
}
