/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.inverse;

import search.Solver;
import variables.Variable;

public class GIC2 extends GICAdvanced {

	protected int timestamp;

	protected int[][] stamps;

	public GIC2(Solver solver) {
		super(solver);
		stamps = Variable.litterals(solver.pb.variables).intArray();
	}

	protected void handleSolution(Variable x, int a, int[] solution) {
		for (int k = cursor - 1; k >= 0; k--) {
			int id = supVariableNums[k];
			if (stamps[id][solution[id]] != timestamp) {
				stamps[id][solution[id]] = timestamp;
				nValuesToBeSupported[id]--;
			}
		}
	}

	@Override
	protected void handleNewSolution(Variable x, int a) {
		handleSolution(x, a, solver.solManager.lastSolution);
	}

	@Override
	protected void intializationAdvanced() {
		timestamp++;
		nSupVariables = 0;
		for (Variable x : solver.futVars) {
			if (x.dom.size() > 1) {
				nValuesToBeSupported[x.num] = x.dom.size();
				supVariableNums[nSupVariables++] = x.num;
			}
		}
	}

	@Override
	protected boolean isInverseAdvanced(Variable x, int a) {
		return stamps[x.num][a] == timestamp || isInverse(x, a);
	}

}
