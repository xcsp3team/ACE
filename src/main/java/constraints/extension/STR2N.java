/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension;

import java.util.Arrays;

import interfaces.Tags.TagNegative;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * This is STR (Simple Tabular Reduction), optimized version, for filtering negative extension (table) constraints.
 * 
 * @author Christophe Lecoutre
 */
public final class STR2N extends STR1Optimized implements TagNegative {

	/**********************************************************************************************
	 * Implementing interfaces
	 *********************************************************************************************/

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
		Arrays.fill(nMaxConflicts, 0);
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	/**
	 * nConflicts[x][a] indicates, during filtering, the number of valid conflicts encountered with (x,a)
	 */
	private int[][] nConflicts;

	/**
	 * nMaxConflicts[x] indicates, during filtering, the maximum number of valid conflicts for a value of x
	 */
	private int[] nMaxConflicts;

	/**
	 * nValidTuples[x] indicates, during filtering, the number of valid tuples for a value of x
	 */
	private long[] nValidTuples;

	/**
	 * Builds an extension constraint, with STR2N as specific filtering method
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public STR2N(Problem pb, Variable[] scp) {
		super(pb, scp);
		this.nConflicts = Variable.litterals(scp).intArray();
		this.nMaxConflicts = new int[scp.length];
		this.nValidTuples = new long[scp.length];
	}

	private void initializeStructuresBeforeFiltering() {
		sSupSize = 0;
		long nValid = Domain.nValidTuplesBounded(doms);
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			long limit = nValid / doms[x].size();
			if (set.size() >= limit && set.size() >= nMaxConflicts[x]) {
				sSup[sSupSize++] = x;
				Arrays.fill(nConflicts[x], 0);
				nMaxConflicts[x] = 0;
				nValidTuples[x] = limit;
			}
		}
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		int depth = problem.solver.depth();
		initializeStructuresBeforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			if (isValid(tuple)) {
				for (int j = sSupSize - 1; j >= 0; j--) {
					int x = sSup[j];
					int a = tuple[x];
					nMaxConflicts[x] = Math.max(nMaxConflicts[x], ++nConflicts[x][a]);
					if (nConflicts[x][a] == nValidTuples[x]) {
						if (scp[x].dom.remove(a) == false)
							return false;
					} else if (nMaxConflicts[x] + i < nValidTuples[x])
						sSup[j] = sSup[--sSupSize];
				}
			} else
				set.removeAtPosition(i, depth);
		}
		return true;
	}
}
