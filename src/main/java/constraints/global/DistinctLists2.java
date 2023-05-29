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

import static utility.Kit.control;

import java.util.stream.IntStream;

import constraints.ConstraintGlobal;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagNotSymmetric;
import problem.Problem;
import sets.SetSparseReversible;
import variables.Domain;
import variables.Variable;

/**
 * A constraint that ensures that lists/vectors of variables (of same size) are not equal, i.e., do not form the same tuple of values.
 * 
 * @author Christophe Lecoutre
 */
public final class DistinctLists2 extends ConstraintGlobal implements TagNotSymmetric, ObserverOnBacktracksSystematic {

	private boolean areDifferent(int start1, int start2, int[] t) {
		for (int j = 0; j < m; j++)
			if (t[start1 + j] != t[start2 + j])
				return true;
		return false;
	}

	@Override
	public boolean isSatisfiedBy(int[] t) {
		for (int i = 0; i < n; i++)
			for (int ii = i + 1; ii < n; ii++)
				if (!areDifferent(i * m, ii * m, t))
					return false;
		return true;
	}

	@Override
	public void afterProblemConstruction(int p) {
		super.afterProblemConstruction(n);
		this.set = new SetSparseReversible((n * (n - 1)) / 2, p + 1);
	}

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
	}

	@Override
	public boolean isGuaranteedAC() {
		return false;
	}

	private Variable[][] lists;

	private final int n, m;

	private final int[] rows, cols;

	private final int[] offsets;

	private final int[][] sentinels;

	private SetSparseReversible set;

	public DistinctLists2(Problem pb, Variable[][] lists) {
		super(pb, pb.vars(lists));
		this.lists = lists;
		this.n = lists.length; // n rows
		control(n >= 2 && IntStream.range(0, n).allMatch(i -> lists[i].length == lists[0].length));
		this.m = lists[0].length; // m columns
		control(scp.length == n * m, "No variable can occur twice in the specified lists");
		this.rows = new int[scp.length];
		this.cols = new int[scp.length];
		for (int i = 0; i < n; i++)
			for (int j = 0; j < m; j++) {
				int p = positionOf(lists[i][j]);
				rows[p] = i;
				cols[p] = j;
			}
		this.offsets = new int[n];
		for (int i = 1; i < n; i++)
			offsets[i] = offsets[i - 1] + (n - i);
		this.sentinels = new int[n][n];
	}

	private Boolean isSentinelFor(int i, int ii, int j) {
		Domain dx = lists[i][j].dom, dy = lists[ii][j].dom;
		if (dx.size() == 1 && dy.size() == 1)
			return dx.singleValue() == dy.singleValue() ? Boolean.FALSE : Boolean.TRUE;
		// below, this is for a normal sentinel found
		sentinels[i][ii] = j;
		sentinels[ii][i] = j;
		return null;
	}

	private Boolean findSentinel(int i, int ii, int j) {
		int jj = sentinels[i][ii];
		if (jj != j) {
			Boolean b = isSentinelFor(i, ii, jj);
			if (b != Boolean.FALSE)
				return b;
		}
		for (jj = 0; jj < m; jj++) {
			if (jj == j)
				continue;
			Boolean b = isSentinelFor(i, ii, jj);
			if (b != Boolean.FALSE)
				return b;
		}
		return Boolean.FALSE;
	}

	@Override
	public boolean runPropagator(Variable x) {
		int depth = problem.solver.depth();
		Domain dx = x.dom;
		if (dx.size() != 1)
			return true;
		int v = dx.singleValue();
		int p = positionOf(x);
		int i = rows[p], j = cols[p];
		for (int ii = 0; ii < n; ii++) {
			if (ii == i)
				continue;
			int k = offsets[Math.min(i, ii)] + Math.abs(ii - i) - 1;
			if (!set.contains(k))
				continue;
			Domain dy = lists[ii][j].dom;
			if (!dy.containsValue(v)) {
				set.remove(k, depth);
				continue;
			}
			Boolean b = findSentinel(i, ii, j);
			if (b == Boolean.FALSE) { // no other sentinel
				if (dy.removeValue(v) == false)
					return false;
				set.remove(k, depth);
				continue;
			} else if (b == Boolean.TRUE) { // strong sentinel
				set.remove(k, depth);
				continue;
			}
		}
		return true;
	}
}
