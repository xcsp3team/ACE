/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.inverse;

import search.Solver;
import utility.Kit;
import variables.Variable;

public class GIC3 extends GIC2 {

	private int[][][] residues;

	public GIC3(Solver solver) {
		super(solver);
		Variable[] variables = solver.pb.variables;
		this.residues = new int[variables.length][][];
		for (int i = 0; i < variables.length; i++)
			residues[i] = new int[variables[i].dom.initSize()][];
	}

	protected void handleNewSolution(Variable x, int a) {
		int[] solution = solver.solManager.lastSolution;
		handleSolution(x, a, solution);
		if (residues[x.num][a] == null)
			residues[x.num][a] = new int[solver.pb.variables.length];
		Kit.copy(solution, residues[x.num][a]);
	}

	protected boolean isInverseAdvanced(Variable x, int a) {
		if (stamps[x.num][a] == timestamp)
			return true;
		if (residues[x.num][a] != null && Variable.isValidTuple(solver.pb.variables, residues[x.num][a],true)) {
			handleSolution(x, a, residues[x.num][a]);
			return true;
		}
		return isInverse(x, a);
	}

}
