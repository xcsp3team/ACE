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
import problem.cliques.Clique;
import problem.cliques.CliqueManager;
import propagation.order2.SecondOrderConsistency;
import search.Solver;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public class CPC8 extends SecondOrderConsistency {
	protected CliqueManager cliqueManager;

	protected PropagationSetOfValues queue;

	protected int[] nSupports;

	protected boolean strongCPC = true; // hard coding

	public CPC8(Solver solver) {
		super(solver);
		this.cliqueManager = new CliqueManager(solver.pb);
		this.queue = new PropagationSetOfValues(solver.pb);
		this.nSupports = new int[solver.pb.constraints.length];
	}

	protected boolean checkPathConsistencyOfSupport(Constraint c, int[] tuple, Clique clique) {
		if (cliqueManager.getPathSupport(c, tuple, clique, -1) == -1) {
			c.removeTuple(tuple);
			queue.add(c, c.scp[0], tuple[0]).add(c, c.scp[1], tuple[1]);
			return false;
		}
		return true;
	}

	private boolean isCurrTupleConsistentForCliques(Constraint c) {
		int[] tuple = c.tupleManager.currTuple;
		for (Clique clique : cliqueManager.cliques[c.num])
			if (checkPathConsistencyOfSupport(c, tuple, clique) == false)
				return false;
		return true;
	}

	private boolean filterConstraint(Constraint c) {
		int cnt = 0;
		for (boolean foundSupport = c.seekFirstSupport(); foundSupport; foundSupport = c.seekNextSupport())
			if (isCurrTupleConsistentForCliques(c))
				cnt++;
		if (cnt == 0)
			return false; // no more tuples
		nSupports[c.num] = cnt;
		return true;
	}

	protected boolean initialize() {
		for (Constraint c : constraints)
			if (c.scp.length == 2 && cliqueManager.cliques[c.num].length > 0 && filterConstraint(c) == false)
				return false;
		return true;
	}

	private boolean revisePath(Constraint c, Variable x, int a) {
		for (Clique clique : cliqueManager.cliques[c.num]) {
			Constraint cxy = clique.getEdgeConstraint(c, x);
			int p = cxy.positionOf(x);
			int[] tuple = cxy.tupleManager.localTuple;
			for (boolean foundSupport = cxy.seekFirstSupportWith(p, a); foundSupport; foundSupport = cxy.seekNextSupport()) // ConsideringPotentialInvalidity(p,
																															// a, tuple))
				if (!checkPathConsistencyOfSupport(cxy, tuple, clique))
					nSupports[cxy.num]--;
			if (nSupports[cxy.num] == 0)
				return false;
		}
		return true;
	}

	// for strong CPC
	private void removeArcConsistentValues() {
		for (Constraint c : constraints) {
			if (c.scp.length != 2)
				continue;
			Domain[] doms = c.doms;
			for (int i = 0; i < doms.length; i++)
				for (int a = doms[i].first(); a != -1; a = doms[i].next(a))
					if (c.seekFirstSupportWith(i, a) == false)
						doms[i].removeElementary(a);
		}
		Kit.log.info("after removeAC, nbTuplesRemoved=" + nTuplesRemoved + " nbValuesRemoved=" + pb().nValuesRemoved);
	}

	@Override
	public boolean enforceSecondOrderConsistency() {
		if (!initialize())
			return false;
		Kit.log.info("after init PC, nbTuplesRemoved=" + nTuplesRemoved + " nbValuesRemoved=" + pb().nValuesRemoved);
		while (queue.size() > 0) {
			Constraint c = queue.firstConstraint();
			Variable x = queue.firstVariable();
			int a = queue.firstIndex();
			queue.remove(0);
			if (!revisePath(c, x, a))
				return false;
		}
		Kit.log.info("after revise PC, nbTuplesRemoved=" + nTuplesRemoved + " nbValuesRemoved=" + pb().nValuesRemoved);
		if (strongCPC)
			removeArcConsistentValues();
		return true;
	}
}
