/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics.values;

import constraints.Constraint;
import interfaces.TagExperimental;
import propagation.soft.pfc.RDAC;
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
		int best = dx.first();
		double bestScore = scoreOf(best) * scoreCoeff;
		for (int a = dx.next(best); a != -1; a = dx.next(a)) {
			double score = scoreOf(a) * scoreCoeff;
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

	public static final class Conflicts extends HeuristicValuesDynamic {

		public Conflicts(Variable x, boolean antiHeuristic) {
			super(x, antiHeuristic);
		}

		@Override
		public double scoreOf(int a) {
			assert x.isFuture() && dx.isPresent(a);
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
			for (Variable y : x.pb.variables)
				if (y.dom.onlyContainsValue(v))
					cnt++;
			return cnt;
		}
	}

	public static final class Aic extends HeuristicValuesDynamic implements TagExperimental {
		private int[] aic;

		public Aic(Variable x, boolean antiHeuristic) {
			super(x, antiHeuristic);
			this.aic = ((RDAC) x.pb.solver.propagation).aic[x.num];
		}

		@Override
		public double scoreOf(int a) {
			return aic[a];
		}
	}

	public static final class SumMinCosts extends HeuristicValuesDynamic implements TagExperimental {
		private long[] sumMinCosts;

		public SumMinCosts(Variable x, boolean antiHeuristic) {
			super(x, antiHeuristic);
			this.sumMinCosts = ((RDAC) x.pb.solver.propagation).sumMinCosts[x.num];
		}

		@Override
		public double scoreOf(int a) {
			return sumMinCosts[a];
		}
	}

}