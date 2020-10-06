/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension.structures;

import java.util.Arrays;

import constraints.Constraint;
import utility.Kit;
import variables.Variable;

public class NextEqNextDiff extends Table {

	public int[][] firstEq;
	public int[][] nextEq;
	public int[][] nextDiff; // 1D = tuple id, 2D= pos , value=tuple id

	public int[][] sizes;

	private void buildFirstNextEq() {
		Constraint c = firstRegisteredCtr();
		firstEq = Variable.litterals(c.scp).intArray();
		for (int i = 0; i < firstEq.length; i++)
			for (int j = 0; j < firstEq[i].length; j++) {
				firstEq[i][j] = -1;
				for (int k = 0; k < tuples.length; k++)
					if (tuples[k][i] == j) {
						firstEq[i][j] = k;
						break;
					}
			}

		nextEq = new int[tuples.length][c.scp.length];
		int[] tmp = new int[Variable.maxInitDomSize(c.scp)];
		for (int j = 0; j < c.scp.length; j++) {
			Arrays.fill(tmp, -1);
			for (int i = tuples.length - 1; i >= 0; i--) {
				nextEq[i][j] = tmp[tuples[i][j]];
				tmp[tuples[i][j]] = i;
			}
		}
	}

	private void buildNextDiff() {
		Constraint c = firstRegisteredCtr();
		nextDiff = new int[tuples.length][c.scp.length];
		for (int j = 0; j < c.scp.length; j++) {
			int nextTupleId = -1, currIdx = -1;
			for (int i = tuples.length - 1; i >= 0; i--)
				if (tuples[i][j] == currIdx)
					nextDiff[i][j] = nextTupleId;
				else {
					int k = i + 1 == tuples.length ? -1 : i + 1;
					nextDiff[i][j] = k;
					nextTupleId = k;
					currIdx = tuples[i][j];
				}
		}

	}

	private void computeSizes() {
		Constraint c = firstRegisteredCtr();
		sizes = Variable.litterals(c.scp).intArray();
		for (int i = 0; i < firstEq.length; i++)
			for (int j = 0; j < firstEq[i].length; j++) {
				int cnt = 0;
				for (int k = firstEq[i][j]; k != -1; k = nextEq[k][i])
					cnt++;
				sizes[i][j] = cnt;
			}
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		super.storeTuples(tuples, positive);
		buildFirstNextEq();
		buildNextDiff();
		computeSizes();
	}

	public NextEqNextDiff(Constraint c) {
		super(c);
	}

	@Override
	public String toString() {
		return super.toString() + "\nfirstEq:\n" + Kit.join(firstEq) + "\nnextEq\n" + Kit.join(nextEq) + "\nnextDiff\n" + Kit.join(nextDiff) + "\nsizes\n"
				+ Kit.join(sizes);
	}
}
