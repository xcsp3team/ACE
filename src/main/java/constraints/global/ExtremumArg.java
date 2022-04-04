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

import org.xcsp.common.Range;
import org.xcsp.common.Types.TypeRank;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagCallCompleteFiltering;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * The constraints MinimumArg and MaximumArg ensure that the index of the minimal values or maximal values assigned to
 * the variables in the scope of the constraint respects a condition. This is the abstract root class.
 * 
 * @author Christophe Lecoutre
 */
public abstract class ExtremumArg extends ConstraintGlobal implements TagCallCompleteFiltering {

	/**
	 * The list (vector) of variables
	 */
	protected final Variable[] list;

	public ExtremumArg(Problem pb, Variable[] list, Variable ext) {
		super(pb, pb.api.vars(ext, list)); // ext may be null
		this.list = list;
	}

	/**********************************************************************************************
	 * ExtremumArgVar, with its two subclasses MaximumArg and MinimumArg
	 *********************************************************************************************/

	public abstract static class ExtremumArgVar extends ExtremumArg {

		/**
		 * The domain of the variable (used as index of an extremum value in list)
		 */
		protected final Domain idom;

		protected final TypeRank rank;

		public ExtremumArgVar(Problem pb, Variable[] list, Variable index, TypeRank rank) {
			super(pb, list, index);
			this.idom = index.dom;
			this.rank = rank;
			control(list.length > 1 && scp.length == list.length + 1, "vector length = " + list.length);
			control(idom.indexesMatchValues() && idom.initiallyExactly(new Range(list.length))); // For the moment
		}

		@Override
		public int[] symmetryMatching() {
			return IntStream.range(0, scp.length).map(i -> i == 0 ? 1 : 2).toArray();
		}

		@Override
		public boolean isGuaranteedAC() {
			return rank == TypeRank.ANY; // code needs to be refined to reach AC when FIRST and LAST
		}

		// ************************************************************************
		// ***** Constraint MaximumArg
		// ************************************************************************

		public static final class MaximumArg extends ExtremumArgVar {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				int v = t[t[0] + 1];
				for (int i = 1; i < t.length; i++)
					if (t[i] > v)
						return false;
				if (rank == TypeRank.FIRST)
					for (int i = 1; i <= t[0]; i++)
						if (t[i] == v)
							return false;
				if (rank == TypeRank.LAST)
					for (int i = t[0] + 2; i < t.length; i++)
						if (t[i] == v)
							return false;
				return true;
			}

			public MaximumArg(Problem pb, Variable[] list, Variable index, TypeRank rank) {
				super(pb, list, index, rank);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// we compute maxMin and maxMax
				int maxMin = Integer.MIN_VALUE, maxMax = Integer.MIN_VALUE;
				for (int a = idom.first(); a != -1; a = idom.next(a)) {
					maxMin = Math.max(maxMin, list[a].dom.firstValue());
					maxMax = Math.max(maxMax, list[a].dom.lastValue());
				}
				// we remove too large values in other variables (those that cannot be anymore used to be indexed)
				int maxMind = Integer.MIN_VALUE, maxMaxd = Integer.MIN_VALUE; // d for deleted indexes
				for (int a = idom.lastRemoved(); a != -1; a = idom.prevRemoved(a)) {
					if (list[a].dom.removeValuesGT(maxMax) == false)
						return false;
					maxMind = Math.max(maxMind, list[a].dom.firstValue());
					maxMaxd = Math.max(maxMaxd, list[a].dom.lastValue());
				}
				// we remove some values from the domain of the index variable
				int limit = Math.max(maxMin, maxMind);
				for (int a = idom.first(); a != -1; a = idom.next(a)) {
					if (list[a].dom.lastValue() < limit)
						idom.remove(a); // no inconsistency possible
				}
				if (rank == TypeRank.FIRST) {
					boolean safe = false, sing = false;
					for (int a = 0; a < list.length; a++)
						if (list[a].dom.containsValue(maxMax)) {
							if (!idom.contains(a)) {
								if (!safe && list[a].dom.removeValue(maxMax) == false)
									return false;
							} else {
								safe = true;
								if (sing) {
									idom.remove(a); // no inconsistency possible
									maxMind = Math.max(maxMind, list[a].dom.firstValue());
									maxMaxd = Math.max(maxMaxd, list[a].dom.lastValue());
								} else if (list[a].dom.size() == 1)
									sing = true;
							}
						}
				}
				if (rank == TypeRank.LAST) {
					boolean safe = false, sing = false;
					for (int a = list.length - 1; a >= 0; a--)
						if (list[a].dom.containsValue(maxMax)) {
							if (!idom.contains(a)) {
								if (!safe && list[a].dom.removeValue(maxMax) == false)
									return false;
							} else {
								safe = true;
								if (sing) {
									idom.remove(a); // no inconsistency possible
									maxMind = Math.max(maxMind, list[a].dom.firstValue());
									maxMaxd = Math.max(maxMaxd, list[a].dom.lastValue());
								} else if (list[a].dom.size() == 1)
									sing = true;
							}
						}
				}
				if (idom.size() == 1) {
					int a = idom.single();
					if (list[a].dom.removeValuesLT(maxMind) == false)
						return false;
					if (rank == TypeRank.ANY && list[a].dom.firstValue() >= maxMaxd)
						// if (list[a].dom.firstValue() >= maxMaxd - (rank == TypeRank.ANY ? 0 : 1)) // Not correct
						return entailed();

				}
				return true;
			}
		}

		// ************************************************************************
		// ***** Constraint MinimumArg
		// ************************************************************************

		public static final class MinimumArg extends ExtremumArgVar {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				int v = t[t[0] + 1];
				for (int i = 1; i < t.length; i++)
					if (t[i] < v)
						return false;
				if (rank == TypeRank.FIRST)
					for (int i = 1; i <= t[0]; i++)
						if (t[i] == v)
							return false;
				if (rank == TypeRank.LAST)
					for (int i = t[0] + 2; i < t.length; i++)
						if (t[i] == v)
							return false;
				return true;
			}

			public MinimumArg(Problem pb, Variable[] list, Variable index, TypeRank rank) {
				super(pb, list, index, rank);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// we compute minMin and minMax
				int minMin = Integer.MAX_VALUE, minMax = Integer.MAX_VALUE;
				for (int a = idom.first(); a != -1; a = idom.next(a)) {
					minMin = Math.min(minMin, list[a].dom.firstValue());
					minMax = Math.min(minMax, list[a].dom.lastValue());
				}
				// we remove too small values in other variables (those that cannot be anymore used to be indexed)
				int minMind = Integer.MAX_VALUE, minMaxd = Integer.MAX_VALUE; // d for deleted indexes
				for (int a = idom.lastRemoved(); a != -1; a = idom.prevRemoved(a)) {
					if (list[a].dom.removeValuesLT(minMin) == false)
						return false;
					minMind = Math.min(minMind, list[a].dom.firstValue());
					minMaxd = Math.min(minMaxd, list[a].dom.lastValue());
				}
				// we remove some values from the domain of the index variable
				for (int a = idom.first(); a != -1; a = idom.next(a)) {
					if (list[a].dom.firstValue() > minMax || list[a].dom.firstValue() > minMaxd)
						idom.remove(a); // no inconsistency possible
				}
				if (rank == TypeRank.FIRST) {
					boolean safe = false, sing = false;
					for (int a = 0; a < list.length; a++)
						if (list[a].dom.containsValue(minMin)) {
							if (!idom.contains(a)) {
								if (!safe && list[a].dom.removeValue(minMin) == false)
									return false;
							} else {
								safe = true;
								if (sing) {
									idom.remove(a); // no inconsistency possible
									minMind = Math.min(minMind, list[a].dom.firstValue());
									minMaxd = Math.min(minMaxd, list[a].dom.lastValue());
								} else if (list[a].dom.size() == 1)
									sing = true;
							}
						}
				}
				if (rank == TypeRank.LAST) {
					boolean safe = false, sing = false;
					for (int a = list.length - 1; a >= 0; a--)
						if (list[a].dom.containsValue(minMin)) {
							if (!idom.contains(a)) {
								if (!safe && list[a].dom.removeValue(minMin) == false)
									return false;
							} else {
								safe = true;
								if (sing) {
									idom.remove(a); // no inconsistency possible
									minMind = Math.min(minMind, list[a].dom.firstValue());
									minMaxd = Math.min(minMaxd, list[a].dom.lastValue());
								} else if (list[a].dom.size() == 1)
									sing = true;
							}
						}
				}
				if (idom.size() == 1) {
					int a = idom.single();
					if (list[a].dom.removeValuesGT(minMaxd) == false)
						return false;
					if (rank == TypeRank.ANY && list[a].dom.lastValue() <= minMind)
						return entailed();

				}
				return true;
			}
		}
	}

}
