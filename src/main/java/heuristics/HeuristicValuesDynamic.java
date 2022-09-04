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

import static utility.Kit.control;

import java.util.Arrays;

import constraints.Constraint;
import optimization.Optimizable;
import optimization.Optimizer;
import sets.SetDense;
import solver.Solver;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This is the root class for building dynamic value ordering heuristics.
 * 
 * @author Christophe Lecoutre
 */
public abstract class HeuristicValuesDynamic extends HeuristicValues {

	public HeuristicValuesDynamic(Variable x, boolean anti) {
		super(x, anti);
	}

	@Override
	public int computeBestValueIndex() {
		assert dx.size() > 0 : "The domain is empty";
		int best = dx.first();
		double bestScore = scoreOf(best) * multiplier;
		for (int a = dx.next(best); a != -1; a = dx.next(a)) {
			double score = scoreOf(a) * multiplier;
			if (score > bestScore) {
				best = a;
				bestScore = score;
			}
		}
		return best;
	}

	// ************************************************************************
	// ***** Subclasses
	// ************************************************************************

	/**
	 * Heuristic as defined in "Making the First Solution Good!", ICTAI 2017: 1073-1077 by J.-G. Fages and C. Prud'homme
	 */
	public static class Bivs extends HeuristicValuesDynamic {

		/**
		 * Return true if BIVS can be applied to the variable. It depends on the distance of the variable with the
		 * objective and the value of some options.
		 * 
		 * @return true if BIVS can be applied to the variable
		 */
		public boolean canBeApplied() {
			if (options.bivsDistance == 2)
				return true; // because no restriction at all
			// limited form of BIVS according to the distance
			int distance = x.distanceWithObjective();
			return distance == 0 || (distance == 1 && options.bivsDistance > 0);
		}

		protected Solver solver;

		/**
		 * The objective constraint
		 */
		private Optimizable oc;

		/**
		 * Indicates if this is the lower bound (or the upper bound) of the objective constraint that must be considered
		 */
		private boolean lbBased;

		/**
		 * The set of inconsistent value indexes found when performing singleton tests
		 */
		public SetDense inconsistent;

		public Bivs(Variable x, boolean anti) {
			super(x, anti);
			this.solver = x.problem.solver;
			Optimizer optimizer = x.problem.optimizer;
			control(optimizer != null);
			this.oc = optimizer.ctr;
			this.multiplier = optimizer.minimization ? -1 : 1; // multiplier follows minimization/maximization
			this.lbBased = options.bivsOptimistic == optimizer.minimization;
			this.inconsistent = new SetDense(x.dom.initSize());
		}

		@Override
		public int computeBestValueIndex() {
			inconsistent.clear();
			if ((options.bivsFirst && solver.solutions.found > 0) || dx.size() > options.bivsLimit)
				return dx.first(); // First in that case
			return super.computeBestValueIndex();
		}

		@Override
		public final double scoreOf(int a) {
			// System.out.println("trying " + x + " " + a + " " + multiplier);
			solver.assign(x, a);
			boolean consistent = solver.propagation.runAfterAssignment(x);
			long score = 0;
			if (!consistent) {
				inconsistent.add(a);
				score = multiplier == -1 ? Long.MAX_VALUE : Long.MIN_VALUE;
			} else
				score = lbBased ? oc.minCurrentObjectiveValue() : oc.maxCurrentObjectiveValue();
			solver.backtrack(x);
			return score;
		}
	}

	/**
	 * BIVS with solution saving as tie-breaker
	 */
	public static final class Bivs2 extends Bivs {

		public Bivs2(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		public int computeBestValueIndex() {
			inconsistent.clear();
			int last = solver.solutions.found == 0 ? -1 : solver.solutions.last[x.num];
			if ((options.bivsFirst && solver.solutions.found > 0) || dx.size() > options.bivsLimit) {
				if (last != -1 && dx.contains(last))
					return last; // solution saving in that case
				return dx.first(); // First in that case
			}
			int best = dx.first();
			double bestScore = scoreOf(best) * multiplier;
			for (int a = dx.next(best); a != -1; a = dx.next(a)) {
				double score = scoreOf(a) * multiplier;
				if (score > bestScore || (score == bestScore && a == last)) {
					// tie breaking by solution saving in priority
					best = a;
					bestScore = score;
				}
			}
			return best;
		}
	}

	public static final class Conflicts extends HeuristicValuesDynamic {

		public Conflicts(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		public double scoreOf(int a) {
			assert !x.assigned() && dx.contains(a);
			long nConflicts = 0;
			for (Constraint c : x.ctrs)
				nConflicts += c.nConflictsFor(c.positionOf(x), a);
			return nConflicts;
		}
	}

	public static final class Failures extends HeuristicValuesDynamic {

		private int[] nDecisions;

		public int[] failed;

		public Failures(Variable x, boolean anti) {
			super(x, anti);
			this.nDecisions = Kit.repeat(1, dx.initSize()); // we use 1 for avoiding divisions by 0
		}

		@Override
		public double scoreOf(int a) {
			return failed[a] / (double) nDecisions[a];
		}

		@Override
		public int computeBestValueIndex() {
			int a = super.computeBestValueIndex();
			nDecisions[a]++;
			return a;
		}
	}

	/**
	 * This heuristic selects a value according to the number of times this value is assigned to the other variables.
	 */
	public static final class Occurrences extends HeuristicValuesDynamic {

		private long last = -1;

		private int[] counts;

		public Occurrences(Variable x, boolean anti) {
			super(x, anti);
			this.counts = new int[dx.initSize()];
		}

		@Override
		public double scoreOf(int a) {
			if (dx.size() == 1)
				return 0; // we don't care about the score returned because the domain is singleton
			if (last != x.problem.solver.stats.safeNumber()) {
				// System.out.println("commpuuu " + x.problem.solver.stats.safeNumber());
				Arrays.fill(counts, 0);
				Variable[] vars = x.problem.varEntities.varToVarArray.containsKey(x) ? (Variable[]) x.problem.varEntities.varToVarArray.get(x).flatVars
						: x.problem.variables; // we reasdon on the array where x belongs if it exists
				for (Variable y : vars) {
					// System.out.println("hhhh " + y);
					Domain dom = y.dom;
					if (dom.size() == 1) {
						if (dx.typeIdentifier() == dom.typeIdentifier())
							counts[dom.single()]++;
						else {
							int b = dx.toIdxIfPresent(dom.singleValue());
							if (b != -1)
								counts[b]++;
						}
					}
				}
				last = x.problem.solver.stats.safeNumber();
			}
			return counts[a];

			// System.out.println("hhh " + x.problem.varEntities.varToVarArray.get(x));

			// int v = dx.toVal(a);
			// int cnt = 0;
			// // TODO bad complexity O(nd) whereas we could have O(n+d)
			// for (Variable y : x.problem.variables)
			// if (y.dom.containsOnlyValue(v))
			// cnt++;
			// return cnt;
		}
	}

}