/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics;

import constraints.Constraint;
import optimization.Optimizable;
import sets.SetDense;
import solver.Solver;
import utility.Kit;
import variables.Variable;

/**
 * This class gives the description of a dynamic value ordering heuristic.
 */
public abstract class HeuristicValuesDynamic extends HeuristicValues {

	public HeuristicValuesDynamic(Variable x, boolean antiHeuristic) {
		super(x, antiHeuristic);
	}

	@Override
	public int identifyBestValueIndex() {
		assert dx.size() != 0 : "The domain is empty";
		// System.out.println("\nchoosing for " + x);
		int best = dx.first();
		double bestScore = scoreOf(best) * scoreCoeff;
		for (int a = dx.next(best); a != -1; a = dx.next(a)) {
			double score = scoreOf(a) * scoreCoeff;
			if (score > bestScore) {
				best = a;
				bestScore = score;
			}
		}
		// System.out.println("choosing " + x + " " + best);
		return best;
	}

	// ************************************************************************
	// ***** Subclasses
	// ************************************************************************

	public static final class Bivs extends HeuristicValuesDynamic {
		Solver solver;

		Optimizable c;

		boolean stoppedAtFirstSolution = true; // hard coding

		boolean promise;

		int nTests;

		public SetDense inconsistent;

		public Bivs(Variable x, boolean antiHeuristic) {
			super(x, antiHeuristic);
			Kit.control(x.problem.optimizer != null);
			this.scoreCoeff = x.problem.optimizer.minimization ? -1 : 1; // scoreCoeff follows minimization/maximization
			this.promise = !antiHeuristic;
			this.solver = x.problem.solver;
			this.c = x.problem.optimizer.ctr;
			this.inconsistent = new SetDense(x.dom.initSize());
		}

		@Override
		public int identifyBestValueIndex() {
			inconsistent.clear();
			if (stoppedAtFirstSolution && solver.solManager.found > 0)
				return dx.first(); // First in that case
			else
				return super.identifyBestValueIndex();
		}

		@Override
		public double scoreOf(int a) {
			// System.out.println("trying " + x + " " + a + " " + scoreCoeff);
			solver.assign(x, a);
			boolean consistent = solver.propagation.runAfterAssignment(x);
			long score = 0;
			if (!consistent) {
				inconsistent.add(a);
				score = scoreCoeff == -1 ? Long.MAX_VALUE : Long.MIN_VALUE;
			} else
				score = promise ? c.maxCurrentObjectiveValue() : c.minCurrentObjectiveValue();
			// if (x.id().equals("k"))
			// System.out.println("score of " + x + " " + a + " : " + score);
			solver.backtrack(x);
			nTests++;
			return score;
		}

	}

	public static final class Conflicts extends HeuristicValuesDynamic {

		public Conflicts(Variable x, boolean antiHeuristic) {
			super(x, antiHeuristic);
		}

		@Override
		public double scoreOf(int a) {
			assert x.isFuture() && dx.present(a);
			long nConflicts = 0;
			for (Constraint c : x.ctrs)
				nConflicts += c.nConflictsFor(c.positionOf(x), a);
			return nConflicts;
		}
	}

	public static final class Failures extends HeuristicValuesDynamic {

		private int[] nDecisions;
		private int[] nFailedDecisions;
		private long[] sumFailedDecisionsHeights; // for the moment, unused

		public void updateWith(int a, int depth, boolean consistent) {
			nDecisions[a]++;
			if (!consistent) {
				nFailedDecisions[a]++;
				sumFailedDecisionsHeights[a] += depth;
			}
		}

		public Failures(Variable x, boolean antiHeuristic) {
			super(x, antiHeuristic);
			this.nDecisions = Kit.repeat(1, dx.initSize()); // we use 1 for avoiding divisions by 0
			this.nFailedDecisions = new int[dx.initSize()];
			this.sumFailedDecisionsHeights = new long[dx.initSize()];
		}

		@Override
		public double scoreOf(int a) {
			// combining with sumFailedDecisionsHeights ?
			return nFailedDecisions[a] / (double) nDecisions[a];
		}
	}

	/**
	 * This heuristic selects a value according to the number of times this value is assigned to the other variables.
	 */
	public static final class Occurrences extends HeuristicValuesDynamic {
		public Occurrences(Variable x, boolean antiHeuristic) {
			super(x, antiHeuristic);
		}

		@Override
		public double scoreOf(int a) {
			int v = x.dom.toVal(a);
			int cnt = 0;
			for (Variable y : x.problem.variables)
				if (y.dom.onlyContainsValue(v))
					cnt++;
			return cnt;
		}
	}

}