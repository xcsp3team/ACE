/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.partial;

import search.Solver;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public class SACPartialMulti extends SACPartial {
	private int[][] residues; // 1D = variable id ; 2D = order; value = residue

	private int[] nResidues; // 1D = vari

	public SACPartialMulti(Solver solver) {
		super(solver);
		residues = Variable.litterals(solver.pb.variables).intArray();
		nResidues = new int[solver.pb.variables.length];
	}

	protected int makeSingletonTestsOn(Variable x) {
		Domain dom = x.dom;
		int sizeBefore = dom.size();
		boolean mustContinue = true;
		int num = x.num;
		for (int i = 0; i < nResidues[num]; i++) {
			int residue = residues[num][i];
			if (dom.isPresent(residue)) {
				if (!checkSAC(x, residue)) {
					x.dom.removeElementary(residue);
				} else {
					mustContinue = false;
					Kit.swap(residues[num], --nResidues[num], i);
					i--;
				}
			}
		}
		if (mustContinue) {
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				if (!checkSAC(x, a)) {
					x.dom.removeElementary(a);
					residues[num][nResidues[num]] = a;
					nResidues[num]++;
				} else
					break;
			}
		}
		return sizeBefore - dom.size();
	}
}
