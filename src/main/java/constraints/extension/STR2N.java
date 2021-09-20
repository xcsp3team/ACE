/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension;

import java.util.Arrays;

import constraints.ConstraintExtension.ExtensionSpecific;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import interfaces.Tags.TagNegative;
import problem.Problem;
import sets.SetDenseReversible;
import variables.Domain;
import variables.Variable;

public class STR2N extends ExtensionSpecific implements TagNegative {

	/**********************************************************************************************
	 * Implementing interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.tuples = ((Table) extStructure).tuples;
		this.set = new SetDenseReversible(tuples.length, problem.variables.length + 1);
		this.nConflicts = Variable.litterals(scp).intArray();
		this.nMaxConflicts = new int[scp.length];
		this.nValidTuples = new long[scp.length];
		this.sSup = new int[scp.length];
	}

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
		Arrays.fill(nMaxConflicts, 0);
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	protected int[][] tuples; // redundant field (reference to tuples in Table)

	protected SetDenseReversible set;

	protected int[][] nConflicts; // nConflicts[x][a] indicates the number of conflicts in the current table for (x,a)

	protected int[] nMaxConflicts; // nMaxConflicts[x] indicates the maximum number of conflicts in the current table
									// for a value of x

	protected long[] nValidTuples; // 1D = variable position

	protected int sSupSize;
	protected int[] sSup;

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
	}

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new Table(this);
	}

	protected void initializeStructuresBeforeFiltering() {
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
