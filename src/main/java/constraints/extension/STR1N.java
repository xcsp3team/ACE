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

import interfaces.Tags.TagNegative;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * This is STR (Simple Tabular Reduction) for filtering negative extension (table) constraints.
 * 
 * @author Christophe Lecoutre
 */
public final class STR1N extends STR1 implements TagNegative {

	/**
	 * nConflicts[x][a] indicates, during filtering, the number of valid conflicts encountered with (x,a)
	 */
	private final int[][] nConflicts;

	/**
	 * Builds an extension constraint, with STR1N as specific filtering method
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public STR1N(Problem pb, Variable[] scp) {
		super(pb, scp);
		this.nConflicts = Variable.litterals(scp).intArray();
	}

	@Override
	protected void beforeFiltering() {
		super.beforeFiltering();
		for (int i = futvars.limit; i >= 0; i--)
			Arrays.fill(nConflicts[futvars.dense[i]], 0);
	}

	@Override
	public boolean runPropagator(Variable evt) {
		int depth = problem.solver.depth();
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			if (isValid(tuple)) {
				for (int j = futvars.limit; j >= 0; j--) {
					int x = futvars.dense[j];
					int a = tuple[x];
					nConflicts[x][a]++;
				}
			} else
				set.removeAtPosition(i, depth);
		}
		long nValidTuples = Domain.nValidTuplesBounded(doms);
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			Domain dom = scp[x].dom;
			long limit = nValidTuples / dom.size();
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				if (nConflicts[x][a] != limit) {
					cnt--;
					cnts[x]--;
					ac[x][a] = true;
				}
			}
		}
		return updateDomains();
	}
}
