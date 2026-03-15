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

import java.util.ArrayList;
import java.util.List;

import solver.Solver;
import solver.Solver.Stopping;
import variables.Variable;

/**
 * Root lower-bound tree search modeled after CP-SAT's {@code LbTreeSearch}.
 *
 * ACE does not expose SAT decision levels for both polarities, so the tree is
 * persisted explicitly and the solver is replayed from the root when we move
 * from one open node to another. The structural invariants still match the
 * OR-Tools design:
 * <ul>
 * <li>each node stores a bound for both branches,</li>
 * <li>bounds only flow upward through the tree,</li>
 * <li>only the root bound is published globally,</li>
 * <li>sub-branches stop being explored once they are above the current root
 * bound.</li>
 * </ul>
 */
final class LbTreeSearch {

	private static final double EPS = 1e-6;
	private static final int NO_CHILD = -1;

	private enum BranchStatus {
		OPEN, ALREADY_SATISFIED, IMPOSSIBLE
	}

	private static final class Node {
		int decisionVariable = -1;
		int decisionValueIndex = -1;

		long trueObjective;
		long falseObjective;

		int trueChild = NO_CHILD;
		int falseChild = NO_CHILD;

		boolean deleted;
		boolean terminal;

		Node(long initialObjective) {
			this.trueObjective = initialObjective;
			this.falseObjective = initialObjective;
		}

		boolean hasDecision() {
			return decisionVariable != -1;
		}

		long objective(boolean minimization) {
			return minimization ? Math.min(trueObjective, falseObjective) : Math.max(trueObjective, falseObjective);
		}

		void updateObjective(long value, boolean minimization) {
			trueObjective = minimization ? Math.max(trueObjective, value) : Math.min(trueObjective, value);
			falseObjective = minimization ? Math.max(falseObjective, value) : Math.min(falseObjective, value);
		}

		void updateTrueObjective(long value, boolean minimization) {
			trueObjective = minimization ? Math.max(trueObjective, value) : Math.min(trueObjective, value);
		}

		void updateFalseObjective(long value, boolean minimization) {
			falseObjective = minimization ? Math.max(falseObjective, value) : Math.min(falseObjective, value);
		}
	}

	private static final class BranchState {
		final long bound;
		final double[] lpValues;

		BranchState(long bound, double[] lpValues) {
			this.bound = bound;
			this.lpValues = lpValues;
		}
	}

	private static final class Decision {
		final Variable variable;
		final int valueIndex;

		Decision(Variable variable, int valueIndex) {
			this.variable = variable;
			this.valueIndex = valueIndex;
		}
	}

	private static final class Selection {
		final ArrayList<Integer> path;
		final Boolean branchToExpand;

		Selection(ArrayList<Integer> path, Boolean branchToExpand) {
			this.path = path;
			this.branchToExpand = branchToExpand;
		}

		int activeNodeIndex() {
			return path.get(path.size() - 1);
		}
	}

	private static final class DiveDecision {
		final int variableNum;
		final int valueIndex;
		final boolean trueBranch;

		DiveDecision(int variableNum, int valueIndex, boolean trueBranch) {
			this.variableNum = variableNum;
			this.valueIndex = valueIndex;
			this.trueBranch = trueBranch;
		}
	}

	private static final class StepOutcome {
		final DiveDecision decision;
		final BranchState state;

		StepOutcome(DiveDecision decision, BranchState state) {
			this.decision = decision;
			this.state = state;
		}
	}

	private static final class CompressionResult {
		final ArrayList<DiveDecision> decisions;
		final long bound;

		CompressionResult(ArrayList<DiveDecision> decisions, long bound) {
			this.decisions = decisions;
			this.bound = bound;
		}
	}

	private final Optimizer optimizer;
	private final Solver solver;
	private final LPRelaxation relaxation;
	private final boolean minimization;
	private final long incumbentCutoff;
	private final int nodeLimit;

	private final boolean hasLp;
	private final boolean exactLpModel;

	private final ArrayList<Node> nodes = new ArrayList<>();

	private long publishedBound;
	private int createdNodes;
	private boolean stop;

	LbTreeSearch(Optimizer optimizer, LPRelaxation relaxation, long incumbentCutoff, int nodeLimit) {
		this.optimizer = optimizer;
		this.solver = optimizer.problem.solver;
		this.relaxation = relaxation;
		this.minimization = optimizer.minimization;
		this.incumbentCutoff = incumbentCutoff;
		this.nodeLimit = nodeLimit;
		this.hasLp = relaxation != null && relaxation.isViable();
		this.exactLpModel = hasLp && relaxation.isFullyLinearizedConstraints();
	}

	int exploredNodes() {
		return createdNodes;
	}

	Long search() {
		if (nodeLimit <= 0)
			return null;

		Stopping stoppingBeforeSearch = solver.stopping;
		boolean auxiliaryModeEnabled = false;
		try {
			if (!resetToRootState())
				return infeasibleProofBound();
			solver.auxiliaryTreeSearchMode = true;
			auxiliaryModeEnabled = true;

			publishedBound = minimization ? optimizer.minBound : optimizer.maxBound;
			nodes.clear();
			nodes.add(new Node(publishedBound));
			createdNodes = 1;
			stop = false;

			BranchState rootState = currentBranchState();
			nodes.get(0).updateObjective(rootState.bound, minimization);
			publishFromRoot();

			while (!stop && !treeClosed()) {
				Selection selection = selectOpenNode();
				if (selection == null)
					break;
				if (!replayPath(selection.path))
					continue;

				Node active = nodes.get(selection.activeNodeIndex());
				BranchState state = currentBranchState();
				active.updateObjective(state.bound, minimization);
				propagateObjectives(selection.path);
				publishFromRoot();
				if (treeClosed() || branchClosed(active.objective(minimization)))
					continue;

				if (active.hasDecision()) {
					boolean changed = normalizeImpossibleBranches(active);
					if (changed) {
						propagateObjectives(selection.path);
						publishFromRoot();
						if (treeClosed() || branchClosed(active.objective(minimization)))
							continue;
					}
				}

				dive(selection.path, selection.branchToExpand, state);
			}
			return publishedBound;
		} finally {
			if (auxiliaryModeEnabled)
				resetToRootState();
			solver.auxiliaryTreeSearchMode = false;
			solver.stopping = stoppingBeforeSearch;
		}
	}

	private boolean treeClosed() {
		return minimization ? publishedBound > incumbentCutoff : publishedBound < incumbentCutoff;
	}

	private void dive(ArrayList<Integer> path, Boolean firstBranch, BranchState baseState) {
		final long threshold = publishedBound;
		int nodeIndex = path.get(path.size() - 1);
		Node node = nodes.get(nodeIndex);
		if (node.deleted || node.terminal || branchClosed(node.objective(minimization)))
			return;

		BranchState startState = baseState;
		if (firstBranch != null) {
			startState = followBranch(node, firstBranch.booleanValue(), path);
			if (startState == null || crossedThreshold(startState.bound, threshold))
				return;
		}

		CompressionResult rawDive = collectFreeDive(startState, threshold);
		if (rawDive == null) {
			if (firstBranch == null && !node.hasDecision())
				node.terminal = true;
			return;
		}

		CompressionResult compressedDive = compressDive(path, firstBranch, rawDive.decisions, threshold);
		if (compressedDive == null)
			return;
		appendCompressedDive(path, firstBranch, compressedDive, threshold);
	}

	private CompressionResult collectFreeDive(BranchState startState, long threshold) {
		ArrayList<DiveDecision> decisions = new ArrayList<>();
		BranchState state = startState;

		while (!stop) {
			Decision decision = chooseDecision(state.lpValues);
			if (decision == null)
				return null;
			StepOutcome outcome = takeDiveDecision(decision);
			decisions.add(outcome.decision);
			state = outcome.state;
			if (crossedThreshold(state.bound, threshold))
				return new CompressionResult(decisions, state.bound);
		}
		return null;
	}

	private StepOutcome takeDiveDecision(Decision decision) {
		Variable x = decision.variable;
		int a = decision.valueIndex;
		if (solver.performBoundTreeAssignment(x, a))
			return new StepOutcome(new DiveDecision(x.num, a, true), currentBranchState());
		if (solver.performBoundTreeRefutation(x, a))
			return new StepOutcome(new DiveDecision(x.num, a, false), currentBranchState());
		return new StepOutcome(new DiveDecision(x.num, a, false), new BranchState(infeasibleProofBound(), null));
	}

	private CompressionResult compressDive(List<Integer> path, Boolean firstBranch, List<DiveDecision> decisions, long threshold) {
		ArrayList<DiveDecision> best = new ArrayList<>(decisions);
		Long bestBound = replayDive(path, firstBranch, best, threshold);
		if (bestBound == null)
			return null;

		for (int i = 0; i < best.size();) {
			ArrayList<DiveDecision> candidate = new ArrayList<>(best);
			candidate.remove(i);
			Long candidateBound = replayDive(path, firstBranch, candidate, threshold);
			if (candidateBound != null) {
				best = candidate;
				bestBound = candidateBound;
			} else
				i++;
		}
		return new CompressionResult(best, bestBound);
	}

	private Long replayDive(List<Integer> path, Boolean firstBranch, List<DiveDecision> decisions, long threshold) {
		if (!resetToRootState())
			return infeasibleProofBound();
		if (!replayKnownPath(path))
			return null;

		Node active = nodes.get(path.get(path.size() - 1));
		if (firstBranch != null) {
			Boolean status = applyRecordedDecision(active.decisionVariable, active.decisionValueIndex, firstBranch.booleanValue());
			if (status == null)
				return null;
			if (!status.booleanValue())
				return infeasibleProofBound();
		}

		for (DiveDecision decision : decisions) {
			Boolean status = applyRecordedDecision(decision.variableNum, decision.valueIndex, decision.trueBranch);
			if (status == null)
				return null;
			if (!status.booleanValue())
				return infeasibleProofBound();
		}

		BranchState state = currentBranchState();
		return crossedThreshold(state.bound, threshold) ? state.bound : null;
	}

	private boolean replayKnownPath(List<Integer> path) {
		for (int i = 0; i + 1 < path.size(); i++) {
			Node node = nodes.get(path.get(i));
			if (node.deleted || !node.hasDecision())
				return false;
			int child = path.get(i + 1);
			boolean trueBranch;
			if (child == node.trueChild)
				trueBranch = true;
			else if (child == node.falseChild)
				trueBranch = false;
			else
				return false;
			Boolean status = applyRecordedDecision(node.decisionVariable, node.decisionValueIndex, trueBranch);
			if (status == null || !status.booleanValue())
				return false;
		}
		return true;
	}

	private Boolean applyRecordedDecision(int variableNum, int valueIndex, boolean trueBranch) {
		Variable x = optimizer.problem.variables[variableNum];
		BranchStatus status = branchStatus(x, valueIndex, trueBranch);
		if (status == BranchStatus.IMPOSSIBLE)
			return null;
		if (status == BranchStatus.ALREADY_SATISFIED)
			return Boolean.TRUE;
		boolean consistent = trueBranch ? solver.performBoundTreeAssignment(x, valueIndex) : solver.performBoundTreeRefutation(x, valueIndex);
		return consistent ? Boolean.TRUE : Boolean.FALSE;
	}

	private void appendCompressedDive(ArrayList<Integer> path, Boolean firstBranch, CompressionResult result, long threshold) {
		ArrayList<DiveDecision> decisions = result.decisions;
		Node active = nodes.get(path.get(path.size() - 1));
		ArrayList<Integer> extendedPath = new ArrayList<>(path);

		if (firstBranch != null) {
			if (decisions.isEmpty()) {
				updateBranchObjective(active, firstBranch.booleanValue(), result.bound);
				propagateObjectives(extendedPath);
				publishFromRoot();
				return;
			}
			int childIndex = attachDecisionChild(active, firstBranch.booleanValue(), decisions.get(0), threshold);
			if (childIndex == NO_CHILD)
				return;
			extendedPath.add(childIndex);
			Node current = nodes.get(childIndex);
			for (int i = 1; i < decisions.size(); i++) {
				childIndex = attachDecisionChild(current, decisions.get(i - 1).trueBranch, decisions.get(i), threshold);
				if (childIndex == NO_CHILD)
					return;
				extendedPath.add(childIndex);
				current = nodes.get(childIndex);
			}
			updateBranchObjective(current, decisions.get(decisions.size() - 1).trueBranch, result.bound);
			propagateObjectives(extendedPath);
			publishFromRoot();
			return;
		}

		if (decisions.isEmpty()) {
			active.terminal = true;
			return;
		}

		DiveDecision firstDecision = decisions.get(0);
		active.decisionVariable = firstDecision.variableNum;
		active.decisionValueIndex = firstDecision.valueIndex;
		Node current = active;
		for (int i = 1; i < decisions.size(); i++) {
			int childIndex = attachDecisionChild(current, decisions.get(i - 1).trueBranch, decisions.get(i), threshold);
			if (childIndex == NO_CHILD)
				return;
			extendedPath.add(childIndex);
			current = nodes.get(childIndex);
		}
		updateBranchObjective(current, decisions.get(decisions.size() - 1).trueBranch, result.bound);
		propagateObjectives(extendedPath);
		publishFromRoot();
	}

	private BranchState followBranch(Node node, boolean trueBranch, List<Integer> path) {
		Variable x = optimizer.problem.variables[node.decisionVariable];
		int a = node.decisionValueIndex;
		BranchStatus status = branchStatus(x, a, trueBranch);
		if (status == BranchStatus.IMPOSSIBLE) {
			markBranchAsInfeasible(node, trueBranch);
			propagateObjectives(path);
			publishFromRoot();
			return null;
		}
		if (status == BranchStatus.OPEN) {
			boolean consistent = trueBranch ? solver.performBoundTreeAssignment(x, a) : solver.performBoundTreeRefutation(x, a);
			if (!consistent) {
				markBranchAsInfeasible(node, trueBranch);
				propagateObjectives(path);
				publishFromRoot();
				return null;
			}
		}

		BranchState state = currentBranchState();
		if (trueBranch)
			node.updateTrueObjective(state.bound, minimization);
		else
			node.updateFalseObjective(state.bound, minimization);
		propagateObjectives(path);
		publishFromRoot();
		return state;
	}

	private int createChild(Node parent, boolean trueBranch, long initialObjective) {
		Node child = new Node(initialObjective);
		nodes.add(child);
		int childIndex = nodes.size() - 1;
		createdNodes++;
		if (trueBranch)
			parent.trueChild = childIndex;
		else
			parent.falseChild = childIndex;
		return childIndex;
	}

	private int attachDecisionChild(Node parent, boolean parentBranch, DiveDecision decision, long initialObjective) {
		if (createdNodes >= nodeLimit) {
			stop = true;
			return NO_CHILD;
		}
		int child = createChild(parent, parentBranch, initialObjective);
		Node childNode = nodes.get(child);
		childNode.decisionVariable = decision.variableNum;
		childNode.decisionValueIndex = decision.valueIndex;
		return child;
	}

	private void updateBranchObjective(Node node, boolean trueBranch, long bound) {
		if (trueBranch)
			node.updateTrueObjective(bound, minimization);
		else
			node.updateFalseObjective(bound, minimization);
	}

	private boolean replayPath(List<Integer> path) {
		if (path.isEmpty())
			return false;
		if (!resetToRootState()) {
			nodes.get(0).updateObjective(infeasibleProofBound(), minimization);
			publishFromRoot();
			return false;
		}

		for (int i = 0; i + 1 < path.size(); i++) {
			Node node = nodes.get(path.get(i));
			if (node.deleted || !node.hasDecision())
				return false;

			int child = path.get(i + 1);
			boolean trueBranch;
			if (child == node.trueChild)
				trueBranch = true;
			else if (child == node.falseChild)
				trueBranch = false;
			else
				return false;

			Variable x = optimizer.problem.variables[node.decisionVariable];
			int a = node.decisionValueIndex;
			BranchStatus status = branchStatus(x, a, trueBranch);
			if (status == BranchStatus.IMPOSSIBLE) {
				markBranchAsInfeasible(node, trueBranch);
				propagateObjectives(path.subList(0, i + 1));
				publishFromRoot();
				return false;
			}
			if (status == BranchStatus.OPEN) {
				boolean consistent = trueBranch ? solver.performBoundTreeAssignment(x, a) : solver.performBoundTreeRefutation(x, a);
				if (!consistent) {
					markBranchAsInfeasible(node, trueBranch);
					propagateObjectives(path.subList(0, i + 1));
					publishFromRoot();
					return false;
				}
			}

			BranchState state = currentBranchState();
			if (trueBranch)
				node.updateTrueObjective(state.bound, minimization);
			else
				node.updateFalseObjective(state.bound, minimization);
			nodes.get(child).updateObjective(state.bound, minimization);
			propagateObjectives(path.subList(0, i + 2));
			publishFromRoot();
			if (crossedThreshold(state.bound, publishedBound) || treeClosed())
				return false;
		}
		return true;
	}

	private Selection selectOpenNode() {
		if (nodes.isEmpty() || nodes.get(0).deleted || branchClosed(nodes.get(0).objective(minimization)))
			return null;
		return selectOpenNode(0, new ArrayList<>());
	}

	private Selection selectOpenNode(int nodeIndex, ArrayList<Integer> path) {
		if (nodeIndex == NO_CHILD)
			return null;
		Node node = nodes.get(nodeIndex);
		if (node.deleted || branchClosed(node.objective(minimization)))
			return null;

		path.add(nodeIndex);
		try {
			if (node.terminal)
				return null;
			if (!node.hasDecision())
				return new Selection(new ArrayList<>(path), null);

			boolean preferTrue = preferredBranch(node);
			Selection selection = selectBranch(node, path, preferTrue);
			if (selection != null)
				return selection;
			return selectBranch(node, path, !preferTrue);
		} finally {
			path.remove(path.size() - 1);
		}
	}

	private Selection selectBranch(Node node, ArrayList<Integer> path, boolean trueBranch) {
		long branchObjective = trueBranch ? node.trueObjective : node.falseObjective;
		if (branchClosed(branchObjective) || prunesAgainstIncumbent(branchObjective))
			return null;
		int child = trueBranch ? node.trueChild : node.falseChild;
		if (child == NO_CHILD || nodes.get(child).deleted)
			return new Selection(new ArrayList<>(path), Boolean.valueOf(trueBranch));
		return selectOpenNode(child, path);
	}

	private boolean normalizeImpossibleBranches(Node node) {
		Variable x = optimizer.problem.variables[node.decisionVariable];
		int a = node.decisionValueIndex;
		boolean changed = false;
		if (branchStatus(x, a, true) == BranchStatus.IMPOSSIBLE) {
			markBranchAsInfeasible(node, true);
			changed = true;
		}
		if (branchStatus(x, a, false) == BranchStatus.IMPOSSIBLE) {
			markBranchAsInfeasible(node, false);
			changed = true;
		}
		return changed;
	}

	private BranchStatus branchStatus(Variable x, int a, boolean trueBranch) {
		boolean contains = x.dom.contains(a);
		if (trueBranch) {
			if (!contains)
				return BranchStatus.IMPOSSIBLE;
			if (x.assigned())
				return BranchStatus.ALREADY_SATISFIED;
			return BranchStatus.OPEN;
		}
		if (!contains)
			return BranchStatus.ALREADY_SATISFIED;
		if (x.assigned())
			return BranchStatus.IMPOSSIBLE;
		return BranchStatus.OPEN;
	}

	private Decision chooseDecision(double[] lpValues) {
		Decision decision = lpValues != null ? chooseLpDecision(lpValues) : null;
		if (decision != null)
			return decision;

		Variable x = solver.heuristic.bestVariable();
		if (x == Variable.TAG)
			return null;
		return new Decision(x, x.heuristic.bestValueIndex());
	}

	private Decision chooseLpDecision(double[] lpValues) {
		Variable bestVariable = null;
		int bestValueIndex = -1;
		double bestFractionality = EPS;

		for (Variable x : solver.futVars) {
			if (x.dom.size() <= 1)
				continue;
			double value = lpValues[x.num];
			double fractional = Math.abs(value - Math.rint(value));
			if (fractional <= bestFractionality)
				continue;
			int valueIndex = x.dom.indexOfValueClosestTo((int) Math.round(value));
			if (valueIndex == -1)
				continue;
			bestFractionality = fractional;
			bestVariable = x;
			bestValueIndex = valueIndex;
		}
		return bestVariable == null ? null : new Decision(bestVariable, bestValueIndex);
	}

	private BranchState currentBranchState() {
		long cpBound = minimization ? optimizer.ctr.minCurrentObjectiveValue() : optimizer.ctr.maxCurrentObjectiveValue();
		double[] lpValues = null;

		if (hasLp) {
			relaxation.updateDomains();
			LPRelaxation.SolveResult lpResult = relaxation.solveWithReducedCostFixing(false, incumbentCutoff, minimization);
			if (lpResult.hasObjectiveBound()) {
				long lpBound = relaxation.roundObjectiveBound(lpResult.objectiveValue, minimization);
				cpBound = minimization ? Math.max(cpBound, lpBound) : Math.min(cpBound, lpBound);
				lpValues = lpResult.variableValues;
			} else if (lpResult.isInfeasible() && exactLpModel) {
				return new BranchState(infeasibleProofBound(), null);
			}
		}
		return new BranchState(cpBound, lpValues);
	}

	private void propagateObjectives(List<Integer> path) {
		for (int i = path.size() - 1; i > 0; i--) {
			Node child = nodes.get(path.get(i));
			Node parent = nodes.get(path.get(i - 1));
			if (parent.trueChild == path.get(i))
				parent.updateTrueObjective(child.objective(minimization), minimization);
			else if (parent.falseChild == path.get(i))
				parent.updateFalseObjective(child.objective(minimization), minimization);
		}
	}

	private boolean preferredBranch(Node node) {
		return minimization ? node.trueObjective <= node.falseObjective : node.trueObjective >= node.falseObjective;
	}

	private boolean branchClosed(long bound) {
		return minimization ? bound > publishedBound : bound < publishedBound;
	}

	private boolean crossedThreshold(long bound, long threshold) {
		return minimization ? bound > threshold : bound < threshold;
	}

	private boolean prunesAgainstIncumbent(long bound) {
		return minimization ? bound > incumbentCutoff : bound < incumbentCutoff;
	}

	private void publishFromRoot() {
		long candidate = nodes.get(0).objective(minimization);
		long safeCandidate = clampToGlobalBound(candidate);
		if (minimization ? safeCandidate > publishedBound : safeCandidate < publishedBound)
			publishedBound = safeCandidate;
	}

	private long clampToGlobalBound(long candidate) {
		if (minimization && candidate > incumbentCutoff)
			return infeasibleProofBound();
		if (!minimization && candidate < incumbentCutoff)
			return infeasibleProofBound();
		return candidate;
	}

	private long infeasibleProofBound() {
		if (minimization)
			return incumbentCutoff == Long.MAX_VALUE ? Long.MAX_VALUE : incumbentCutoff + 1;
		return incumbentCutoff == Long.MIN_VALUE ? Long.MIN_VALUE : incumbentCutoff - 1;
	}

	private void markBranchAsInfeasible(Node node, boolean trueBranch) {
		int child = trueBranch ? node.trueChild : node.falseChild;
		if (trueBranch) {
			node.updateTrueObjective(infeasibleProofBound(), minimization);
			node.trueChild = NO_CHILD;
		} else {
			node.updateFalseObjective(infeasibleProofBound(), minimization);
			node.falseChild = NO_CHILD;
		}
		markSubtreeAsDeleted(child);
	}

	private void markSubtreeAsDeleted(int root) {
		if (root == NO_CHILD)
			return;
		ArrayList<Integer> toDelete = new ArrayList<>();
		toDelete.add(root);
		for (int i = 0; i < toDelete.size(); i++) {
			int nodeIndex = toDelete.get(i);
			if (nodeIndex == NO_CHILD || nodeIndex >= nodes.size())
				continue;
			Node node = nodes.get(nodeIndex);
			if (node.deleted)
				continue;
			node.deleted = true;
			toDelete.add(node.trueChild);
			toDelete.add(node.falseChild);
		}
	}

	private boolean resetToRootState() {
		solver.restoreProblem();
		return solver.propagation == null || solver.propagation.runInitially();
	}
}
