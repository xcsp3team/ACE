/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order2.path;

import constraints.CtrHard;
import problem.cliques.CliqueManager;
import search.Solver;
import variables.Variable;

public class PC2001 extends PC8 {

	private int[][][][] last;

	public PC2001(Solver solver) {
		super(solver);
		last = new int[hards.length][][][];
		for (CtrHard c : hards)
			if (c.scp.length == 2)
				last[c.num] = new int[c.scp[0].dom.initSize()][c.scp[1].dom.initSize()][solver.pb.variables.length];
	}

	@Override
	protected boolean checkPathConsistencyOfSupport(CtrHard cxy, int[] support, Variable z) {
		Variable x = cxy.scp[0], y = cxy.scp[1];
		int a = support[0], b = support[1];
		CtrHard cxz = (z.num > x.num ? constraintsAccess[z.num][x.num] : constraintsAccess[x.num][z.num]);
		CtrHard cyz = (z.num > y.num ? constraintsAccess[z.num][y.num] : constraintsAccess[y.num][z.num]);
		int c = CliqueManager.getPathSupport(x, y, a, b, z, last[cxy.num][support[0]][support[1]][z.num], cxz, cyz);
		if (c == -1) {
			cxy.removeTuple(support);
			queue.add(cxy, x, a).add(cxy, y, b);
			return false;
		}
		last[cxy.num][support[0]][support[1]][z.num] = c;
		return true;
	}
}
