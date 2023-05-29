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

import org.xcsp.common.Utilities;

import constraints.ConstraintGlobal;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import interfaces.Tags.TagNotCallCompleteFiltering;
import interfaces.Tags.TagNotSymmetric;
import problem.Problem;
import sets.SetSparseReversible;
import variables.Domain;
import variables.Variable;

/**
 * A constraint that ensures that two lists/vectors of variables (of same size) are not equal, i.e., do not form the same tuple of values. IMPORTANT: for the
 * moment, when the same variable occurs several times, AC is not guaranteed. We find 279360 solutions for: <br />
 * java ace Crossword-ogd-p02.xml -s=all -varh=Dom -g_dv=1 // intension <br />
 * java ace Crossword-ogd-p02.xml -s=all -varh=Dom -g_dv=1 -hybrid // smart tables <br />
 * java ace Crossword-ogd-p02.xml -s=all -varh=Dom // distinct lists
 * 
 * @author Christophe Lecoutre
 */
public abstract class DistinctLists extends ConstraintGlobal implements TagNotSymmetric, ObserverOnBacktracksSystematic {

	public DistinctLists(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	/**********************************************************************************************
	 * DistinctLists2
	 *********************************************************************************************/

	public final static class DistinctLists2 extends DistinctLists implements TagCallCompleteFiltering {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			for (int i = 0; i < half; i++)
				if (t[pos1[i]] != t[pos2[i]])
					return true;
			return false;
		}

		@Override
		public void restoreBefore(int depth) {
			if (uniqueSentinelLevel == depth)
				uniqueSentinelLevel = -1;
		}

		@Override
		public boolean isGuaranteedAC() {
			return scp.length == 2 * half; // AC is guaranteed if not several occurrences of the same variable
		}

		/**
		 * A first list (actually array) of variables
		 */
		private final Variable[] list1;

		/**
		 * A second list (actually array) of variables
		 */
		private final Variable[] list2;

		/**
		 * pos1[i] is the position of the variable list1[i] in the constraint scope
		 */
		private final int[] pos1;

		/**
		 * pos2[i] is the position of the variable list2[i] in the constraint scope
		 */
		private final int[] pos2;

		/**
		 * The size of the lists (half of the scope size)
		 */
		private final int half;

		/**
		 * Initial mode: two sentinels for tracking the presence of different values.
		 */
		private int sentinel1, sentinel2;

		/**
		 * Possible mode: only one remaining sentinel, identified at a certain level
		 */
		private int uniqueSentinel, uniqueSentinelLevel = -1;

		/**
		 * Build a constraint DistinctLists for the specified problem over the two specified lists of variables
		 * 
		 * @param pb
		 *            the problem to which the constraint is attached
		 * @param list1
		 *            a first list of variables
		 * @param list2
		 *            a second list of variables
		 */
		public DistinctLists2(Problem pb, Variable[] list1, Variable[] list2) {
			super(pb, pb.vars(list1, list2));
			this.half = list1.length;
			this.list1 = list1;
			this.list2 = list2;
			control(1 < half && half == list2.length && IntStream.range(0, half).allMatch(i -> list1[i] != list2[i]));
			this.pos1 = IntStream.range(0, half).map(i -> Utilities.indexOf(list1[i], scp)).toArray();
			this.pos2 = IntStream.range(0, half).map(i -> Utilities.indexOf(list2[i], scp)).toArray();
			this.sentinel1 = 0;
			this.sentinel2 = half - 1;
		}

		private boolean handleUniqueSentinel(Domain dom1, Domain dom2) {
			if (dom1.size() > 1 && dom2.size() > 1)
				return true;
			if (dom1.size() == 1)
				return dom2.removeValueIfPresent(dom1.singleValue()) && entailed();
			return dom1.removeValueIfPresent(dom2.singleValue()) && entailed();
		}

		private boolean isGoodSentinel(Domain dom1, Domain dom2) {
			return dom1.size() > 1 || dom2.size() > 1 || dom1.singleValue() != dom2.singleValue();
		}

		private int findAnotherSentinel() {
			for (int i = 0; i < half; i++)
				if (i != sentinel1 && i != sentinel2 && isGoodSentinel(list1[i].dom, list2[i].dom))
					return i;
			return -1;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (uniqueSentinelLevel != -1)
				return handleUniqueSentinel(list1[uniqueSentinel].dom, list2[uniqueSentinel].dom);

			Domain dx1 = list1[sentinel1].dom, dx2 = list2[sentinel1].dom, dy1 = list1[sentinel2].dom, dy2 = list2[sentinel2].dom;
			if (dx1.size() == 1 && dx2.size() == 1) { // possibly, sentinel1 is no more valid
				if (dx1.singleValue() != dx2.singleValue())
					return entailed();
				int sentinel = findAnotherSentinel();
				if (sentinel != -1) {
					sentinel1 = sentinel;
					dx1 = list1[sentinel1].dom;
					dx2 = list2[sentinel1].dom;
				} else {
					uniqueSentinel = sentinel2;
					uniqueSentinelLevel = problem.solver.depth();
					return handleUniqueSentinel(dy1, dy2);
				}
			}
			if (dy1.size() == 1 && dy2.size() == 1) { // possibly, sentinel2 is no more valid
				if (dy1.singleValue() != dy2.singleValue())
					return entailed();
				int sentinel = findAnotherSentinel();
				if (sentinel != -1) {
					sentinel2 = sentinel;
				} else {
					uniqueSentinel = sentinel1;
					uniqueSentinelLevel = problem.solver.depth();
					return handleUniqueSentinel(dx1, dx2);
				}
			}
			return true;
		}
	}

	/**********************************************************************************************
	 * DistinctListsK
	 *********************************************************************************************/

	public final static class DistinctListsK extends DistinctLists implements TagNotAC, TagNotCallCompleteFiltering {

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
			super.afterProblemConstruction(p);
			this.set = new SetSparseReversible((n * (n - 1)) / 2, p + 1);
		}

		@Override
		public void restoreBefore(int depth) {
			set.restoreLimitAtLevel(depth);
		}

		private Variable[][] lists;

		private int n, m;

		private final int[] rows, cols;

		private final int[] offsets;

		private final int[][] sentinels;

		private SetSparseReversible set;

		public DistinctListsK(Problem pb, Variable[][] lists) {
			super(pb, pb.vars(lists));
			this.lists = lists;
			this.n = lists.length; // n rows
			control(n >= 2 && IntStream.range(0, n).allMatch(i -> lists[i].length == lists[0].length));
			this.m = lists[0].length; // m columns
			control(m >= 2 && scp.length == n * m, "No variable can occur twice in the specified lists");
			this.rows = new int[scp.length];
			this.cols = new int[scp.length];
			for (int i = 0; i < n; i++)
				for (int j = 0; j < m; j++) {
					int p = positionOf(lists[i][j]);
					rows[p] = i;
					cols[p] = j;
				}
			this.offsets = new int[n - 1];
			for (int i = 1; i < offsets.length; i++)
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

		private Boolean findSentinel(int i, int ii, int jToIgnore) {
			int j = sentinels[i][ii];
			if (j != jToIgnore) {
				Boolean b = isSentinelFor(i, ii, j);
				if (b != Boolean.FALSE)
					return b;
			}
			for (j = 0; j < m; j++) {
				if (j == jToIgnore)
					continue;
				Boolean b = isSentinelFor(i, ii, j);
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

}
