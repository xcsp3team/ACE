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
import heuristics.HeuristicValuesDynamic.HeuristicUsingAssignments.TagRequireFailedPerValue;
import heuristics.HeuristicValuesDynamic.HeuristicUsingAssignments.TagRequirePerValue;
import interfaces.Tags.TagMaximize;
import optimization.Optimizable;
import optimization.Optimizer;
import sets.SetDense;
import solver.Solver;
import solver.Statistics.VarAssignments;
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
			// System.out.println("check " + score + " " + bestScore);
			if (score > bestScore) {
				// System.out.println("better " + score + " " + bestScore);
				best = a;
				bestScore = score;
			}
		}
		// System.out.println("best " + bestScore);
		return best;
	}

	// ************************************************************************
	// ***** Specific heuristics
	// ************************************************************************

	/**
	 * This heuristic selects a value according to the number of times this value is assigned to the other variables.
	 */
	public static class Occs extends HeuristicValuesDynamic {

		protected final int[] nOccurrences;

		private final Variable[] variablesOfInterest; // we reason on the array where x belongs if it exists

		private long last = -1;

		public Occs(Variable x, boolean anti) {
			super(x, anti);
			this.nOccurrences = new int[dx.initSize()];
			this.variablesOfInterest = variablesOfInterest();
		}

		protected void updateFrom(Domain dom) {
			if (dom.size() == 1) {
				if (dx.typeIdentifier() == dom.typeIdentifier())
					nOccurrences[dom.single()]++;
				else {
					int b = dx.toIdxIfPresent(dom.singleValue());
					if (b != -1)
						nOccurrences[b]++;
				}
			}
		}

		@Override
		public double scoreOf(int a) {
			if (dx.size() == 1)
				return 0; // we don't care about the score returned because the domain is singleton
			if (last != x.problem.solver.stats.safeNumber()) {
				Arrays.fill(nOccurrences, 0);
				for (Variable y : variablesOfInterest)
					updateFrom(y.dom);
				last = x.problem.solver.stats.safeNumber();
			}
			return nOccurrences[a];
		}
	}

	public static class OccsR extends Occs { // refined Occs

		private static int[] COEFFS = new int[] { 0, 10, 5, 3, 2, 2 }; // score for domains of size 1 to 5

		public OccsR(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		protected void updateFrom(Domain dom) {
			if (dom.size() < COEFFS.length) { // TODO hard coding : only reasoning with domains of size at most 5
				int coeff = COEFFS[dom.size()];
				if (dx.typeIdentifier() == dom.typeIdentifier()) {
					for (int a = dom.first(); a != -1; a = dom.next(a))
						nOccurrences[a] += coeff;
				} else {
					for (int a = dom.first(); a != -1; a = dom.next(a)) {
						int b = dx.toIdxIfPresent(dom.toVal(a));
						if (b != -1)
							nOccurrences[b] += coeff;
					}
				}
			}
		}
	}

	public static abstract class HeuristicUsingAssignments extends HeuristicValuesDynamic {

		public interface TagRequirePerValue {
		}

		public interface TagRequireFailedPerValue {
		}

		public VarAssignments assignments; // will be defined when constructing Assignments

		public HeuristicUsingAssignments(Variable x, boolean anti) {
			super(x, anti);
		}
	}

	public static class Asgs extends HeuristicUsingAssignments implements TagRequirePerValue {

		public Asgs(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		public double scoreOf(int a) {
			return assignments.nPerValue[a];
		}
	}

	// Asgs enlarged to the array
	public static class AsgsE extends HeuristicUsingAssignments implements TagRequirePerValue {
		private final int[] t;

		private final Variable[] variablesOfInterest; // we reason on the array where x belongs if it exists

		private long last = -1;

		public AsgsE(Variable x, boolean anti) {
			super(x, anti);
			this.t = new int[dx.initSize()];
			this.variablesOfInterest = variablesOfInterest();
		}

		@Override
		public double scoreOf(int a) {
			if (dx.size() == 1)
				return 0; // we don't care about the score returned because the domain is singleton
			if (last != x.problem.solver.stats.safeNumber()) {
				for (int b = dx.first(); b != -1; b = dx.next(b))
					t[b] = assignments.nPerValue[b];
				for (Variable y : variablesOfInterest) {
					Domain dom = y.dom;
					if (dom.size() == 1) {
						int b = dom.single();
						if (dx.typeIdentifier() == dom.typeIdentifier())
							t[b] += assignments.nPerValue[b];
						else {
							int c = dx.toIdxIfPresent(dom.toVal(b));
							if (c != -1)
								t[c] += assignments.nPerValue[b];
						}
					}
				}
				last = x.problem.solver.stats.safeNumber();
			}
			return t[a];
		}
	}

	public static final class AsgsFp extends Asgs implements TagRequireFailedPerValue {

		public AsgsFp(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		public double scoreOf(int a) {
			return assignments.nPerValue[a] + 2 * assignments.nFailedPerValue[a]; // WHY 2 as coeff ?
		}
	}

	public static final class AsgsFm extends Asgs implements TagRequireFailedPerValue {

		public AsgsFm(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		public double scoreOf(int a) {
			return assignments.nPerValue[a] - 2 * assignments.nFailedPerValue[a];
		}
	}

	public static class Flrs extends HeuristicUsingAssignments implements TagRequireFailedPerValue {

		public Flrs(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		public double scoreOf(int a) {
			return assignments.nFailedPerValue[a];
		}
	}

	public static final class FlrsR extends Flrs implements TagRequirePerValue {

		public FlrsR(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		public double scoreOf(int a) {
			return assignments.nPerValue[a] == 0 ? 0 : assignments.nFailedPerValue[a] / (double) assignments.nPerValue[a];
		}
	}

	// Flrs enlarged to the array
	public static class FlrsE extends Flrs {
		private final int[] t;

		private final Variable[] variablesOfInterest; // we reason on the array where x belongs if it exists

		private long last = -1;

		public FlrsE(Variable x, boolean anti) {
			super(x, anti);
			this.t = new int[dx.initSize()];
			this.variablesOfInterest = variablesOfInterest();
		}

		@Override
		public double scoreOf(int a) {
			if (dx.size() == 1)
				return 0; // we don't care about the score returned because the domain is singleton
			if (last != x.problem.solver.stats.safeNumber()) {
				for (int b = dx.first(); b != -1; b = dx.next(b))
					t[b] = assignments.nFailedPerValue[b];
				for (Variable y : variablesOfInterest) {
					Domain dom = y.dom;
					if (dom.size() == 1) {
						int b = dom.single();
						if (dx.typeIdentifier() == dom.typeIdentifier())
							t[b] += assignments.nFailedPerValue[b];
						else {
							int c = dx.toIdxIfPresent(dom.toVal(b));
							if (c != -1)
								t[c] += assignments.nFailedPerValue[b];
						}
					}
				}
				last = x.problem.solver.stats.safeNumber();
			}
			return t[a];
		}
	}

	public static class Dist extends HeuristicValuesDynamic {

		private final Variable[] variablesOfInterest; // we reason on the array where x belongs if it exists

		public Dist(Variable x, boolean anti) {
			super(x, anti);
			this.variablesOfInterest = variablesOfInterest();
		}

		@Override
		public double scoreOf(int a) {
			if (dx.size() == 1)
				return 0; // we don't care about the score returned because the domain is singleton
			int v = dx.toVal(a);
			int d = 0;
			for (Variable y : variablesOfInterest)
				if (y.dom.size() == 1)
					d += Math.abs(v - y.dom.singleValue());
			return d;
		}
	}

	// ************************************************************************
	// ***** BIVS variants
	// ************************************************************************

	/**
	 * Heuristic as defined in "Making the First Solution Good!", ICTAI 2017: 1073-1077 by J.-G. Fages and C. Prud'homme
	 */
	public static class Bivs extends HeuristicValuesDynamic {

		/**
		 * Return true if BIVS can be applied to the variable. It depends on the distance of the variable with the objective and the value of some options.
		 * 
		 * @return true if BIVS can be applied to the variable
		 */
		public boolean canBeApplied() {
			if (options.bivsDistance == 2)
				return true; // because no restriction at all limited form of BIVS according to the distance
			int distance = x.distanceWithObjective();
			return distance == 0 || (distance == 1 && options.bivsDistance > 0);
		}

		protected Solver solver;

		/**
		 * The objective constraint
		 */
		protected Optimizable oc;

		/**
		 * Indicates if this is the lower bound (or the upper bound) of the objective constraint that must be considered
		 */
		protected boolean lbBased;

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
			// if ((options.bivsFirst && solver.solutions.found > 0) || dx.size() > options.bivsLimit)
			// return dx.first(); // First in that case
			return super.computeBestValueIndex();
		}

		@Override
		public double scoreOf(int a) {
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
			int last = solver.solutions.found == 0 ? -1 : solver.solutions.last.idxs[x.num];
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

	// public static final class Bivs3 extends Bivs {
	//
	// public Bivs3(Variable x, boolean anti) {
	// super(x, anti);
	// }
	//
	// @Override
	// public int computeBestValueIndex() {
	// Variable[] h1 = x.problem.solver.solutions.h1;
	// boolean present = Utilities.indexOf(x, h1) >= 0;
	// if (!present)
	// return x.dom.first();
	// return super.computeBestValueIndex();
	// }
	// }

	// ************************************************************************
	// ***** Other heuristics
	// ************************************************************************

	// This class cannot be really used as defined below (large arity is highly problematic)
	public static final class Conflicts extends HeuristicValuesDynamic {

		public Conflicts(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		public double scoreOf(int a) {
			assert !x.assigned() && dx.contains(a);
			long nConflicts = 0;
			for (Constraint c : x.ctrs)
				nConflicts += c.nConflictsFor(c.positionOf(x), a); // Very expensive
			return nConflicts;
		}
	}

	public static final class InternDist extends HeuristicValuesDynamic implements TagMaximize {

		public InternDist(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		public double scoreOf(int a) {
			int v = dx.toVal(a);
			int prev = dx.prev(a), next = dx.next(a);
			int score = (prev == -1 ? 0 : v - dx.toVal(prev)) + (next == -1 ? 0 : dx.toVal(next) - v);
			// System.out.println("score " + score);
			return score;
		}
	}

}