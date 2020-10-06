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
import problem.cliques.Clique;
import search.Solver;

public class CPC2001 extends CPC8 {

	private int[][][][] last; // vid - idx(firsVar)-idx(secondVar)-cliqueOrder

	public CPC2001(Solver solver) {
		super(solver);
		last = new int[solver.pb.constraints.length][][][];
		for (CtrHard c : hards) {
			if (c.scp.length != 2)
				continue;
			int k = cliqueManager.cliques[c.num].length;
			if (k > 0)
				last[c.num] = new int[c.scp[0].dom.initSize()][c.scp[1].dom.initSize()][k];
		}
	}

	@Override
	protected boolean checkPathConsistencyOfSupport(CtrHard cxy, int[] tuple, Clique clique) {
		int cliquePosition = clique.getPositionOf(cxy);
		int c = cliqueManager.getPathSupport(cxy, tuple, clique, last[cxy.num][tuple[0]][tuple[1]][cliquePosition]);
		if (c == -1) {
			cxy.removeTuple(tuple);
			queue.add(cxy, cxy.scp[0], tuple[0]).add(cxy, cxy.scp[1], tuple[1]);
			return false;
		}
		last[cxy.num][tuple[0]][tuple[1]][cliquePosition] = c;
		return true;
	}
}
