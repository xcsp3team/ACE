/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package heuristics;

import variables.Variable;

/**
 * This is the root class for building direct value ordering heuristics, i.e., heuristics for which we directly know
 * which value index has to be returned (most of the time, without searching)
 * 
 * @author Christophe Lecoutre
 */
public abstract class HeuristicValuesDirect extends HeuristicValues {

	public HeuristicValuesDirect(Variable x, boolean dummy) {
		super(x, dummy); // dummy because has no influence with such heuristics
	}

	@Override
	protected double scoreOf(int a) {
		throw new AssertionError("The value must be directly selected without any iteration");
	}

	// ************************************************************************
	// ***** Subclasses
	// ************************************************************************

	public static final class First extends HeuristicValuesDirect {
		public First(Variable x, boolean dummy) {
			super(x, dummy);
		}

		@Override
		public int computeBestValueIndex() {
			return dx.first();
		}
	}

	public static final class Last extends HeuristicValuesDirect {
		public Last(Variable x, boolean dummy) {
			super(x, dummy);
		}

		@Override
		public int computeBestValueIndex() {
			return dx.last();
		}
	}

	public static final class Median extends HeuristicValuesDirect {
		public Median(Variable x, boolean dummy) {
			super(x, dummy);
		}

		@Override
		public int computeBestValueIndex() {
			int a = dx.first();
			for (int cnt = dx.size() / 2; cnt > 0; cnt--)
				a = dx.next(a);
			return a;
		}
	}

	public static final class Rand extends HeuristicValuesDirect {
		public Rand(Variable x, boolean dummy) {
			super(x, dummy);
		}

		@Override
		public int computeBestValueIndex() {
			return dx.any();
		}
	}

	/**
	 * This (meta-)heuristic uses a cycle composed of First, Last and Rand at every new sequence of three runs
	 */
	public static final class RunRobin extends HeuristicValuesDirect {

		public RunRobin(Variable x, boolean dummy) {
			super(x, dummy);
		}

		@Override
		public int computeBestValueIndex() {
			int run = x.problem.solver.restarter.numRun;
			if (run % 3 == 0)
				return dx.first();
			if (run % 3 == 1)
				return dx.last();
			return dx.any();
		}
	}

	/**
	 * This (meta-)heuristic uses a cycle composed of First, Last and Rand at every new sequence of three nodes
	 */
	public static final class Robin extends HeuristicValuesDirect {

		private int cnt = -1;

		public Robin(Variable x, boolean dummy) {
			super(x, dummy);
		}

		@Override
		public int computeBestValueIndex() {
			cnt++;
			if (cnt % 3 == 0)
				return dx.first();
			if (cnt % 3 == 1)
				return dx.last();
			return dx.any();
		}
	}

	public static final class Values extends HeuristicValuesDirect {

		/**
		 * Indicates if one searches to minimize or maximize the number of distinct values
		 */
		private boolean minimize;

		/**
		 * The variables of interest when minimizing (or maximizing) the number of distinct values
		 */
		private Variable[] others;

		public Values(Variable x, boolean anti, Variable[] others) {
			super(x, anti);
			this.minimize = !anti;
			this.others = others;
		}

		@Override
		public int computeBestValueIndex() {
			if (dx.size() == 1)
				return 0; // we don't care about the score returned because the domain is singleton
			if (minimize) { // minimizing the number of distinct values
				for (Variable y : others)
					if (y != x && y.dom.size() == 1) {
						int a = dx.toIdxIfPresent(y.dom.firstValue());
						if (a >= 0)
							return a;
					}
				return dx.first();
			}
			// maximizing the number of distinct values
			throw new AssertionError("max Values not implemented");
		}
	}

}

// public static final class MinCost extends HeuristicValuesDirect implements TagExperimental {
// private int[] argMinSumMinCosts;
//
// public MinCost(Variable x, boolean dummy) {
// super(x, dummy);
// control(x.pb.solver.propagation instanceof PFC);
// argMinSumMinCosts = ((PFC) x.pb.solver.propagation).argMinSumMinCosts;
// }
//
// @Override
// public int computeBestValueIndex() {
// assert dx.isPresent(argMinSumMinCosts[x.num]);
// return argMinSumMinCosts[x.num];
// }
// }
