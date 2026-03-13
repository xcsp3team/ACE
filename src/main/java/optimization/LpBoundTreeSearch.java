/*
 * This file is part of the constraint solver ACE (AbsCon Essence).
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS.
 *
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package optimization;

/**
 * Small LP-only tree search used to raise the root objective bound once a
 * finite incumbent is known. It is inspired by CP-SAT's {@code LbTreeSearch},
 * but deliberately lighter: it branches on fractional LP values and caches the
 * best lower/upper bound that can be proved for each branch with the LP
 * relaxation alone.
 */
final class LpBoundTreeSearch {

	private static final double EPS = 1e-6;

	private static final class BranchOutcome {
		double bound;
		LPRelaxation.SolveResult child;

		BranchOutcome(double bound, LPRelaxation.SolveResult child) {
			this.bound = bound;
			this.child = child;
		}
	}

	private static final class BranchingDecision {
		final int variable;
		final double lowerUpper;
		final double upperLower;

		BranchingDecision(int variable, double lowerUpper, double upperLower) {
			this.variable = variable;
			this.lowerUpper = lowerUpper;
			this.upperLower = upperLower;
		}
	}

	private final LPRelaxation relaxation;
	private final boolean minimization;
	private final long incumbentBound;
	private final int nodeLimit;

	private int exploredNodes;

	LpBoundTreeSearch(LPRelaxation relaxation, boolean minimization, long incumbentBound, int nodeLimit) {
		this.relaxation = relaxation;
		this.minimization = minimization;
		this.incumbentBound = incumbentBound;
		this.nodeLimit = nodeLimit;
	}

	int exploredNodes() {
		return exploredNodes;
	}

	Long search() {
		if (nodeLimit <= 0)
			return null;

		LPRelaxation.SolveResult root = relaxation.solve(false);
		if (root.isInfeasible())
			return infeasibleRoundedBound();
		if (!root.hasObjectiveBound())
			return null;

		exploredNodes = 1;
		double bound = explore(root);
		if (Double.isInfinite(bound))
			return infeasibleRoundedBound();
		return relaxation.roundObjectiveBound(bound, minimization);
	}

	private double explore(LPRelaxation.SolveResult node) {
		double currentBound = node.objectiveValue;
		if (exploredNodes >= nodeLimit || prunesAgainstIncumbent(currentBound))
			return currentBound;

		BranchingDecision decision = pickFractionalVariable(node.variableValues);
		if (decision == null)
			return currentBound;

		BranchOutcome lowerBranch = solveBranch(decision.variable, relaxation.getVariableLowerBound(decision.variable), decision.lowerUpper, currentBound);
		BranchOutcome upperBranch = solveBranch(decision.variable, decision.upperLower, relaxation.getVariableUpperBound(decision.variable), currentBound);

		BranchOutcome first = betterFirst(lowerBranch, upperBranch) ? lowerBranch : upperBranch;
		BranchOutcome second = first == lowerBranch ? upperBranch : lowerBranch;

		expand(first);
		expand(second);

		return minimization ? Math.min(lowerBranch.bound, upperBranch.bound) : Math.max(lowerBranch.bound, upperBranch.bound);
	}

	private void expand(BranchOutcome outcome) {
		if (outcome.child == null || exploredNodes >= nodeLimit || prunesAgainstIncumbent(outcome.bound))
			return;
		outcome.bound = explore(outcome.child);
		outcome.child = null;
	}

	private BranchOutcome solveBranch(int variable, double lower, double upper, double fallbackBound) {
		double oldLower = relaxation.getVariableLowerBound(variable);
		double oldUpper = relaxation.getVariableUpperBound(variable);

		double newLower = Math.max(lower, oldLower);
		double newUpper = Math.min(upper, oldUpper);
		if (newLower > newUpper + EPS)
			return new BranchOutcome(infeasibleBound(), null);
		if (exploredNodes >= nodeLimit)
			return new BranchOutcome(fallbackBound, null);

		relaxation.setVariableBounds(variable, newLower, newUpper);
		LPRelaxation.SolveResult child = relaxation.solve(false);
		exploredNodes++;
		relaxation.setVariableBounds(variable, oldLower, oldUpper);

		if (child.isInfeasible())
			return new BranchOutcome(infeasibleBound(), null);
		if (!child.hasObjectiveBound())
			return new BranchOutcome(fallbackBound, null);
		return new BranchOutcome(child.objectiveValue, child);
	}

	private BranchingDecision pickFractionalVariable(double[] values) {
		int bestVariable = -1;
		double bestScore = EPS;
		double bestLowerUpper = 0d;
		double bestUpperLower = 0d;

		for (int i = 0; i < relaxation.numOriginalVariables(); i++) {
			double value = values[i];
			double lower = relaxation.getVariableLowerBound(i);
			double upper = relaxation.getVariableUpperBound(i);
			double lowerUpper = Math.floor(value);
			double upperLower = Math.ceil(value);
			if (upperLower - lowerUpper < 1d)
				continue;
			if (lowerUpper < lower - EPS || upperLower > upper + EPS)
				continue;

			double fractionalPart = Math.abs(value - Math.rint(value));
			if (fractionalPart > bestScore) {
				bestScore = fractionalPart;
				bestVariable = i;
				bestLowerUpper = lowerUpper;
				bestUpperLower = upperLower;
			}
		}
		return bestVariable == -1 ? null : new BranchingDecision(bestVariable, bestLowerUpper, bestUpperLower);
	}

	private boolean betterFirst(BranchOutcome left, BranchOutcome right) {
		return minimization ? left.bound <= right.bound : left.bound >= right.bound;
	}

	private boolean prunesAgainstIncumbent(double bound) {
		return minimization ? bound > incumbentBound + EPS : bound < incumbentBound - EPS;
	}

	private double infeasibleBound() {
		if (minimization)
			return incumbentBound == Long.MAX_VALUE ? Double.POSITIVE_INFINITY : incumbentBound + 1d;
		return incumbentBound == Long.MIN_VALUE ? Double.NEGATIVE_INFINITY : incumbentBound - 1d;
	}

	private long infeasibleRoundedBound() {
		if (minimization)
			return incumbentBound == Long.MAX_VALUE ? Long.MAX_VALUE : incumbentBound + 1;
		return incumbentBound == Long.MIN_VALUE ? Long.MIN_VALUE : incumbentBound - 1;
	}
}
