/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagNotAC;
import problem.Problem;
import variables.Variable;

/**
 * Experimental
 * 
 * @author Christophe Lecoutre
 */
public final class SubsetAllDifferent extends ConstraintGlobal implements TagNotAC { // not call filtering-complete

	@Override
	public final boolean isSatisfiedBy(int[] t) {
		for (int i = 0; i < subsets.length; i++) {
			Variable[] subset = subsets[i];
			for (int j = 0; j < subset.length; j++)
				for (int k = j + 1; k < subset.length; k++)
					if (t[mapping[i][j]] == t[mapping[i][k]])
						return false;
		}
		return true;
	}

	private final Variable[][] subsets;

	private final boolean[][] irreflexives;

	private final int[][] mapping;

	public SubsetAllDifferent(Problem pb, Variable[][] subsets) {
		super(pb, Utilities.collect(Variable.class, (Object[]) subsets));
		this.subsets = subsets;
		this.mapping = IntStream.range(0, subsets.length)
				.mapToObj(i -> IntStream.range(0, subsets[i].length).map(j -> Utilities.indexOf(subsets[i][j], scp)).toArray()).toArray(int[][]::new);
		int n = pb.features.collecting.variables.size();
		this.irreflexives = new boolean[n][n];
		for (int i = 0; i < subsets.length; i++) {
			Variable[] subset = subsets[i];
			for (int j = 0; j < subset.length; j++) {
				int num1 = subset[j].num;
				for (int k = j + 1; k < subset.length; k++) {
					int num2 = subset[k].num;
					irreflexives[num1][num2] = true;
					irreflexives[num2][num1] = true;
				}
			}
		}
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (x.dom.size() == 1) {
			// ensures basic filtering (like a clique of binary constraints)
			int v = x.dom.singleValue();
			for (int i = futvars.limit; i >= 0; i--) {
				Variable y = scp[futvars.dense[i]];
				if (irreflexives[x.num][y.num] && y != x && y.dom.removeValueIfPresent(v) == false)
					return false;
			}
		}
		return true;
	}
}
