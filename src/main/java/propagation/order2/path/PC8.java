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

import java.util.stream.IntStream;

import constraints.Constraint;
import problem.cliques.CliqueManager;
import propagation.order2.SecondOrderConsistency;
import search.Solver;
import utility.Kit;
import variables.Variable;

public class PC8 extends SecondOrderConsistency {

	protected Constraint[][] constraintsAccess;

	protected PropagationSetOfValues queue;

	protected int[] nSupports;

	public PC8(Solver solver) {
		super(solver);
		constraintsAccess = IntStream.range(0, constraints.length).mapToObj(i -> new Constraint[i]).toArray(Constraint[][]::new);
		int cnt = 0;
		for (Constraint c : constraints) {
			if (c.scp.length != 2)
				continue;
			cnt++;
			int num1 = c.scp[0].num, num2 = c.scp[1].num;
			if (num1 > num2)
				constraintsAccess[num1][num2] = c;
			else
				constraintsAccess[num2][num1] = c;
		}
		Kit.control(cnt == (solver.pb.variables.length * (solver.pb.variables.length - 1)) / 2, () -> "The graph is not complete: use the option -cg=yes. ");

		queue = new PropagationSetOfValues(solver.pb);
		nSupports = new int[solver.pb.constraints.length];
	}

	protected boolean checkPathConsistencyOfSupport(Constraint c, int[] support, Variable z) {
		Variable x = c.scp[0], y = c.scp[1];
		int a = support[0], b = support[1];
		Constraint cxz = (z.num > x.num ? constraintsAccess[z.num][x.num] : constraintsAccess[x.num][z.num]);
		Constraint cyz = (z.num > y.num ? constraintsAccess[z.num][y.num] : constraintsAccess[y.num][z.num]);
		if (CliqueManager.getPathSupport(x, y, a, b, z, -1, cxz, cyz) == -1) {
			c.removeTuple(support);
			queue.add(c, x, a).add(c, y, b);
			return false;
		}
		return true;
	}

	private boolean filterConstraint(Constraint c) {
		int cnt = 0;
		int[] tuple = c.tupleManager.localTuple;
		for (boolean foundSupport = c.seekFirstSupport(); foundSupport; foundSupport = c.seekNextSupport()) {
			boolean consistent = true;
			for (Variable x : solver.pb.variables) {
				if (x == c.scp[0] || x == c.scp[1])
					continue;
				if (checkPathConsistencyOfSupport(c, tuple, x) == false) {
					consistent = false;
					break;
				}
			}
			if (consistent)
				cnt++;
		}
		if (cnt == 0)
			return false; // no more tuples
		nSupports[c.num] = cnt;
		return true;
	}

	protected boolean initialize() {
		for (Constraint c : constraints)
			if (c.scp.length == 2 && !filterConstraint(c))
				return false;
		return true;
	}

	private boolean revisePath(Constraint c, Variable x, int a) {
		Variable z = c.scp[c.scp[0] == x ? 1 : 0];
		for (Variable y : solver.pb.variables) {
			if (y == c.scp[0] || y == c.scp[1])
				continue;
			Constraint cxy = (y.num > x.num ? constraintsAccess[y.num][x.num] : constraintsAccess[x.num][y.num]);
			int p = cxy.positionOf(x);
			int[] tuple = cxy.tupleManager.localTuple;
			for (boolean foundSupport = cxy.seekFirstSupportWith(p, a); foundSupport; foundSupport = cxy.seekNextSupport()) // ConsideringPotentialInvalidity(p,
																															// a, tuple))
				if (!checkPathConsistencyOfSupport(cxy, tuple, z))
					nSupports[cxy.num]--;
			if (nSupports[cxy.num] == 0)
				return false;
		}
		return true;
	}

	@Override
	public boolean enforceSecondOrderConsistency() {
		if (!initialize())
			return false;
		while (queue.size() > 0) {
			Constraint c = queue.firstConstraint();
			Variable x = queue.firstVariable();
			int a = queue.firstIndex();
			queue.remove(0);
			if (!revisePath(c, x, a))
				return false;
		}
		if (!enforceArcConsistency())
			return false;
		Kit.log.info("after revise PC, nbTuplesRemoved=" + nTuplesRemoved + " nbValuesRemoved=" + pb().nValuesRemoved);
		return true;
	}
}
