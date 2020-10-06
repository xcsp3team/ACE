/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension.structures;

import constraints.Constraint;
import utility.Kit;

public class SubTableNextDiff extends SubTable {

	private int[][] nextDiff; // 1D = tuple id, 2D= pos , value=tuple id

	private void buildNextDiff() {
		Constraint ctr = firstRegisteredCtr();
		nextDiff = new int[tuples.length][ctr.scp.length];
		for (int j = 0; j < ctr.scp.length; j++) {
			int nextTupleId = tuples.length, currInd = -1;
			for (int i = tuples.length - 1; i >= 0; i--)
				if (tuples[i][j] == currInd)
					nextDiff[i][j] = nextTupleId;
				else {
					nextDiff[i][j] = i + 1;
					nextTupleId = i + 1;
					currInd = tuples[i][j];
				}
		}
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		super.storeTuples(tuples, positive);
		buildNextDiff();
	}

	public SubTableNextDiff(Constraint ctr) {
		super(ctr);
	}

	@Override
	public String toString() {
		return super.toString() + Kit.join(nextDiff);
	}

}
