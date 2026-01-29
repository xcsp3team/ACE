/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.IntStream;
import java.util.stream.Stream;

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
				for (int k = j + 1; k < subset.length; k++) {
					int v = t[mapping[i][j]], w = t[mapping[i][k]];
					if (exceptValue != null && (v == exceptValue || w == exceptValue))
						continue;
					if (v == w)
						return false;
				}
		}
		return true;
	}

	private final Variable[][] subsets;

	private Integer exceptValue;

	private final int[][] mapping;

	private final boolean[][] irreflexives;

	private int[][] neighbours;

	public SubsetAllDifferent(Problem pb, Variable[][] subsets, Integer exceptValue) {
		super(pb, Utilities.collect(Variable.class, (Object[]) subsets));
		this.subsets = subsets;
		this.exceptValue = exceptValue;
		this.mapping = IntStream.range(0, subsets.length)
				.mapToObj(i -> IntStream.range(0, subsets[i].length).map(j -> Utilities.indexOf(subsets[i][j], scp)).toArray()).toArray(int[][]::new);
		int n = pb.features.collecting.variables.size();
		this.irreflexives = IntStream.range(0, n).mapToObj(i -> new boolean[i + 1]).toArray(boolean[][]::new);
		Set<Integer>[] sets = IntStream.range(0, n).mapToObj(i -> new LinkedHashSet<>()).toArray(Set[]::new);
		for (int i = 0; i < subsets.length; i++) {
			Variable[] subset = subsets[i];
			for (int j = 0; j < subset.length; j++) {
				int num1 = subset[j].num;
				for (int k = j + 1; k < subset.length; k++) {
					int num2 = subset[k].num;
					assert num1 != num2;
					irreflexives[Math.max(num1, num2)][Math.min(num1, num2)] = true;
					sets[num1].add(num2);
					sets[num2].add(num1);
				}
			}
		}
		this.neighbours = Stream.of(sets).map(set -> set.stream().mapToInt(i -> i).sorted().toArray()).toArray(int[][]::new);
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (x.dom.size() == 1) {
			// ensures basic filtering (like a clique of binary constraints)
			int v = x.dom.singleValue();
			if (exceptValue != null && v == exceptValue)
				return true;
			int xnum = x.num;
			int[] t = neighbours[x.num];
			if (futvars.size() < t.length) {
				for (int i = futvars.limit; i >= 0; i--) {
					Variable y = scp[futvars.dense[i]];
					if (y != x && irreflexives[Math.max(xnum, y.num)][Math.min(xnum, y.num)] && y.dom.removeValueIfPresent(v) == false)
						return false;
				}
			} else {
				for (int i = t.length - 1; i >= 0; i--) {
					int ynum = t[i];
					Variable y = problem.variables[ynum];
					if (y != x && irreflexives[Math.max(xnum, ynum)][Math.min(xnum, ynum)] && y.dom.removeValueIfPresent(v) == false)
						return false;
				}
			}
		}
		return true;
	}
}
