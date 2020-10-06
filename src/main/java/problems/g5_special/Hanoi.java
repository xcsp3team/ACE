/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g5_special;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

import utility.operations.Base;

/* Hanoi towers problem." + "\nInitial state: all discs on tower 0" + "\nFinal state: all discs on tower 2 */
public class Hanoi implements ProblemAPI {
	int nDisks;

	private boolean areCompatible(int state1, int state2, int nDiscs, int nTowers) {
		// A state of the Hanoi towers. The array index corresponds to a disc (index 0 = biggest disc, index nDics-1 = smallest disc) The
		// array value corresponds to a tower. For instance, if t[i] = j, then it means that the disc i is put on tower j.
		int[] t1 = Base.baseValueFor(state1, nDiscs, nTowers), t2 = Base.baseValueFor(state2, nDiscs, nTowers);
		boolean[] frozenTowers = new boolean[nTowers];
		int i;
		for (i = t1.length - 1; i >= 0 && t1[i] == t2[i]; i--)
			frozenTowers[t1[i]] = true;
		return i >= 0 && !frozenTowers[t1[i]] && !frozenTowers[t2[i]] && IntStream.range(0, i).allMatch(j -> t1[j] == t2[j]);
	}

	@Override
	public void model() {
		int nTowers = 3, nStates = Utilities.power(nTowers, nDisks), nSteps = Utilities.power(2, nDisks) - 1;

		Var[] x = array("x", size(nSteps - 1), dom(range(nStates)));

		extension(x[0], 1, 2); // first state (after the initial one) with smallest disc on tower 1 or 2 (all others on tower 0)
		int[][] tuples = range(nStates).range(nStates).select((i, j) -> areCompatible(i, j, nDisks, nTowers));
		slide(x, range(nSteps - 2), i -> extension(vars(x[i], x[i + 1]), tuples));
	}

	// belong(x[x.length - 1], set(nStates - 3, nStates - 2)); // last but one state with smallest disc on tower 0 or 1 (all others on tower
	// 2)
}