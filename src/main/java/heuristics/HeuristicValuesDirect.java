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

import interfaces.Tags.TagExperimental;
import variables.Variable;

public abstract class HeuristicValuesDirect extends HeuristicValues {
	public HeuristicValuesDirect(Variable x, boolean dummy) {
		super(x, dummy); // dummy because has no influence with this direct heuristic
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
		public int identifyBestValueIndex() {
			return dx.first();
		}
	}

	public static final class Last extends HeuristicValuesDirect {
		public Last(Variable x, boolean dummy) {
			super(x, dummy);
		}

		@Override
		public int identifyBestValueIndex() {
			return dx.last();
		}
	}

	public static final class Median extends HeuristicValuesDirect {
		public Median(Variable x, boolean dummy) {
			super(x, dummy);
		}

		@Override
		public int identifyBestValueIndex() {
			int a = dx.first();
			for (int cnt = dx.size() / 2; cnt > 0; cnt--)
				a = dx.next(a);
			return a;
		}
	}

	public static class ProgressSaving extends HeuristicValuesDirect implements TagExperimental { // TODO: code to be updated
		private int[] progressSaving;

		public ProgressSaving(Variable x, boolean dummy) {
			super(x, dummy);
			// progressSaving = ((SolverBacktrack) (x.pb.solver)).lcReasoner.getProgressSaving();
		}

		@Override
		public int identifyBestValueIndex() {
			int a = progressSaving[x.num];
			return a != -1 && dx.contains(a) ? a : dx.first();
		}
	}

	public static final class Rand extends HeuristicValuesDirect {
		public Rand(Variable x, boolean dummy) {
			super(x, dummy);
		}

		@Override
		public int identifyBestValueIndex() {
			return dx.any();
		}
	}

	public static final class RunRobin extends HeuristicValuesDirect {

		public RunRobin(Variable x, boolean dummy) {
			super(x, dummy);
		}

		@Override
		public int identifyBestValueIndex() {
			int run = x.problem.solver.restarter.numRun;
			if (run % 3 == 0)
				return dx.first();
			if (run % 3 == 1)
				return dx.last();
			return dx.any();
		}
	}

	public static final class Robin extends HeuristicValuesDirect {
		int cnt = -1;

		public Robin(Variable x, boolean dummy) {
			super(x, dummy);
		}

		@Override
		public int identifyBestValueIndex() {
			cnt++;
			if (cnt % 3 == 0)
				return dx.first();
			if (cnt % 3 == 1)
				return dx.last();
			return dx.any();
		}
	}

	public static final class Values extends HeuristicValuesDirect {

		private boolean min;
		private Variable[] others;

		public Values(Variable x, boolean antiHeuristic, Variable[] others) {
			super(x, antiHeuristic);
			this.min = !antiHeuristic;
			this.others = others;
		}

		@Override
		public int identifyBestValueIndex() {
			if (dx.size() == 1)
				return dx.first();
			if (min) { // to minimize the number of distinct values
				for (Variable y : others)
					if (y != x && y.dom.size() == 1) {
						int a = dx.toIdxIfPresent(y.dom.firstValue());
						if (a >= 0)
							return a;
					}
				return dx.first();
			}
			// to maximize the number of distinct values
			throw new UnsupportedOperationException();
		}
	}

	// public static final class MinCost extends HeuristicValuesDirect implements TagExperimental {
	// private int[] argMinSumMinCosts;
	//
	// public MinCost(Variable x, boolean dummy) {
	// super(x, dummy);
	// Kit.control(x.pb.solver.propagation instanceof PFC);
	// argMinSumMinCosts = ((PFC) x.pb.solver.propagation).argMinSumMinCosts;
	// }
	//
	// @Override
	// public int identifyBestValueIndex() {
	// assert dx.isPresent(argMinSumMinCosts[x.num]);
	// return argMinSumMinCosts[x.num];
	// }
	// }

}
