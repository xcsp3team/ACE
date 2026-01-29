/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package heuristics;

import sets.SetDense;
import variables.Variable;

/**
 * This is the root class for building direct value ordering heuristics, i.e., heuristics for which we directly know which value index has to be returned (most
 * of the time, without searching)
 * 
 * @author Christophe Lecoutre
 */
public abstract class HeuristicValuesDirect extends HeuristicValues {

	public HeuristicValuesDirect(Variable x, boolean anti) {
		super(x, anti);
	}

	@Override
	protected double scoreOf(int a) {
		throw new AssertionError("The value must be directly selected without any iteration");
	}

	// ************************************************************************
	// ***** Specific heuristics
	// ************************************************************************

	public static final class First extends HeuristicValuesDirect {
		public First(Variable x, boolean dummy) {
			super(x, dummy); // dummy because has no influence with such an heuristic
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

	public static final class Vals extends HeuristicValuesDirect {

		public Variable[] variablesOfInterest; // public so as to be able to modify it in some contexts

		private SetDense set;

		public Vals(Variable x, boolean anti) {
			super(x, anti);
			this.variablesOfInterest = variablesOfInterest();
			this.set = anti ? new SetDense(dx.initSize()) : null;
		}

		@Override
		public int computeBestValueIndex() {
			if (dx.size() == 1)
				return 0; // we don't care about the score returned because the domain is singleton
			if (multiplier == -1) { // if minimizing the number of distinct values
				for (Variable y : variablesOfInterest)
					if (y != x && y.dom.size() == 1) {
						int a = dx.toIdxIfPresent(y.dom.singleValue());
						if (a >= 0)
							return a; // because already assigned
					}
			} else { // maximizing the number of distinct values
				set.clear();
				for (Variable y : variablesOfInterest)
					if (y != x && y.dom.size() == 1) {
						int a = dx.toIdxIfPresent(y.dom.singleValue());
						if (a >= 0 && !set.contains(a))
							set.add(a);
					}
				for (int a = dx.first(); a != -1; a = dx.next(a))
					if (!set.contains(a))
						return a; // because not already assigned
			}
			return dx.first(); // if no value being a possible candidate, we return the first value
		}
	}

	// ************************************************************************
	// ***** Combining heuristics
	// ************************************************************************

	/**
	 * This (meta-)heuristic uses a cycle composed of First, Last and Rand at every new sequence of three runs
	 */
	public static final class RunRobin extends HeuristicValuesDirect {

		public RunRobin(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		public int computeBestValueIndex() {
			int mod = x.problem.solver.restarter.numRun % 3;
			if (mod == 0)
				return dx.first();
			if (mod == 1)
				return dx.last();
			return dx.any();
		}

		public String currentClass() {
			int mod = x.problem.solver.restarter.numRun % 3;
			return mod == 0 ? "First" : mod == 1 ? "Last" : "Rand";
		}
	}

	/**
	 * This (meta-)heuristic uses a cycle composed of First, Last and Rand at every new sequence of three nodes
	 */
	public static final class Robin extends HeuristicValuesDirect {

		private int cnt = -1;

		public Robin(Variable x, boolean anti) {
			super(x, anti);
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
