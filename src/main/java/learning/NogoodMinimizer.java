package learning;

import propagation.GAC;
import propagation.Propagation;
import solver.DecisionRecorder;
import solver.Solver;
import utility.Enums.EStopping;
import variables.Variable;

public class NogoodMinimizer {

	private Solver solver;
	private Propagation propagation;
	private DecisionRecorder dr;
	private int arityLimit;

	public NogoodMinimizer(Solver solver) {
		this.solver = solver;
		this.propagation = solver.propagation;
		this.dr = solver.decRecorder;
		this.arityLimit = solver.head.control.learning.nogoodArityLimit;
	}

	private boolean addPositiveTransitionDecision(int positiveDecision, int[] tmp, int nTransitions) {
		tmp[nTransitions] = positiveDecision;
		Variable x = dr.varIn(positiveDecision);
		int a = dr.idxIn(positiveDecision);
		if (!x.dom.present(a))
			return false;
		solver.assign(x, a);
		return propagation.runAfterAssignment(x);
	}

	private int searchPositiveTransitionDecision(int right, int[] decs, int limitDepth) {
		boolean consistent = true;
		int left = 0;
		for (; consistent && left < right; left++) {
			Variable x = dr.varIn(decs[left]);
			int a = dr.idxIn(decs[left]);
			if (!x.dom.present(a)) {
				consistent = false;
			} else {
				solver.assign(x, a);
				consistent = propagation.runAfterAssignment(x);
			}
			assert !consistent || !(propagation instanceof GAC) || ((GAC) propagation).controlArcConsistency();
		}
		if (consistent)
			return -1;
		while (solver.futVars.size() > 0 && solver.depth() != limitDepth - 1)
			solver.backtrack();
		return left - 1;
	}

	public int[] extractMinimalNogoodFrom(int[] decs) {
		int[] tmp = new int[decs.length];
		int positionOfLastFoundTransitionDecision = decs.length - 1; // right excluded
		int nTransitions = 0; // number of found transition decisions
		boolean consistent = addPositiveTransitionDecision(decs[positionOfLastFoundTransitionDecision], tmp, nTransitions++);
		if (!consistent) {
			Variable x = solver.futVars.lastPast();
			int a = x.dom.unique();
			solver.backtrack(x);
			x.dom.removeElementary(a);
			consistent = x.dom.size() > 0 && propagation.runAfterRefutation(x);
			if (!consistent) {
				solver.stopping = EStopping.FULL_EXPLORATION;
				return new int[0];
			}
			return null;
		}
		while (consistent && 0 < positionOfLastFoundTransitionDecision && nTransitions < arityLimit) {
			if (positionOfLastFoundTransitionDecision == 1) {
				tmp[nTransitions++] = decs[0];
				break;
			}
			positionOfLastFoundTransitionDecision = searchPositiveTransitionDecision(positionOfLastFoundTransitionDecision, decs, solver.depth());
			if (positionOfLastFoundTransitionDecision != -1)
				consistent = addPositiveTransitionDecision(decs[positionOfLastFoundTransitionDecision], tmp, nTransitions++);
		}
		solver.backtrackToTheRoot();

		// if (consistent && nbTransitions >=
		// NogoodManager.NOGOOD_SIZE_LIMIT || (right == -1 && nbDecisions >=
		// NogoodManager.NOGOOD_SIZE_LIMIT))
		// return null;

		if (positionOfLastFoundTransitionDecision == -1) {
			int[] t = new int[decs.length];
			for (int i = 0; i < t.length; i++)
				t[i] = -decs[i];
			return t;
		} else {
			int[] t = new int[nTransitions];
			for (int i = 0; i < t.length; i++)
				t[i] = -tmp[i];
			return t;
		}
	}

	// ****************************************/

	// private boolean addTransitionDecisionTo(int indexOfLastTransitionDecision, int[] tmp, int nbFoundTransitionDecisions, int[] decs, int nbDecs) {
	// tmp[nbFoundTransitionDecisions] = decs[indexOfLastTransitionDecision];
	// int limit = Math.max(0, nbFoundTransitionDecisions - 1);
	// while (tmp[limit] < 0)
	// limit--;
	// for (int i = limit; i < nbFoundTransitionDecisions; i++) {
	// Variable x = dr.varIn(tmp[i]);
	// int a = dr.idxIn(tmp[i]);
	// if (tmp[i] > 0) {
	// assert x.dom.isPresent(a);
	// assign(x, a);
	// boolean consistent = propagation.runAfterAssignment(x);
	// assert consistent;
	// } else {
	// assert x.dom.size() > 1 || !x.dom.isPresent(a);
	// if (x.dom.isPresent(a)) {
	// x.dom.removeElementary(a);
	// boolean consistent = x.dom.size() > 0 && propagation.runAfterRefutation(x);
	// assert consistent;
	// }
	// }
	// }
	// Variable x = dr.varIn(decs[indexOfLastTransitionDecision]);
	// int a = dr.idxIn(decs[indexOfLastTransitionDecision]);
	// boolean consistent = true;
	// if (decs[indexOfLastTransitionDecision] > 0) {
	// if (!x.dom.isPresent(a))
	// return false;
	// assign(x, a);
	// consistent = propagation.runAfterAssignment(x);
	// } else {
	// if (x.dom.size() == 1 && x.dom.isPresent(a))
	// return false;
	// if (x.dom.isPresent(a)) {
	// x.dom.removeElementary(a);
	// consistent = x.dom.size() > 0 && propagation.runAfterRefutation(x);
	// }
	// }
	// return consistent;
	// }
	//
	// /**
	// * Returns the index in decisions of the transition decision, or -1 if it is not found. It is possible since we just use the original
	// * constraints of the problem and not the noggods recorded so far (it ssem rather difficult).
	// */
	// private int searchTransitionDecision(int left, int right, int[] decs, int nbDecs, int limitDepth) {
	// boolean consistent = true;
	// for (; left < right && consistent; left++) {
	// Variable x = dr.varIn(decs[left]);
	// int a = dr.idxIn(decs[left]);
	// if (decs[left] > 0) {
	// if (!x.dom.isPresent(a)) {
	// consistent = false;
	// } else {
	// assign(x, a);
	// consistent = propagation.runAfterAssignment(x);
	// }
	// } else {
	// if (x.dom.size() == 1 && x.dom.isPresent(a))
	// consistent = false;
	// else if (x.dom.isPresent(a)) {
	// x.dom.removeElementary(a);
	// consistent = x.dom.size() > 0 && propagation.runAfterRefutation(x);
	// }
	// }
	// assert !consistent || !(propagation instanceof AC) || ((AC) propagation).controlArcConsistency();
	// }
	// if (left == nbDecs - 1 && consistent)
	// return -1;
	// assert !consistent && (left - 1) < right : "cons = " + consistent + " lastPositive = " + (left - 1);
	// while (futVars.size() > 0 && depth() != limitDepth - 1)
	// backtrack();
	// return left - 1;
	// }
	//
	// private int[] extractMinimalNogoodFrom(SolverBacktrack solver, int[] decs, int nbDecs) {
	// propagation.queue.clear();
	// Variable[] variables = pb.variables;
	// // copy of the original problem at depth 0 : it means that all
	// // negative decisions that occur before the first positive one have
	// // been taken into account
	// for (int i = 0; i < variables.length; i++) {
	// Domain dom = solver.pb.variables[i].dom;
	// for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a))
	// if (dom.isRemovedAtLevel(a, 0))
	// variables[i].dom.remove(a, 0);
	// }
	// int[] tmp = new int[nbDecs];
	// int nbFoundTransitionDecisions = 0;
	// boolean consistent = addTransitionDecisionTo(nbDecs - 1, tmp, nbFoundTransitionDecisions++, decs, nbDecs);
	// int initialLeftOffset = 0;
	// while (decs[initialLeftOffset] < 0)
	// initialLeftOffset++;
	// int right = nbDecs - 1; // right excluded
	// while (consistent && nbFoundTransitionDecisions < rs.cp.settingLearning.nogoodArityLimit && initialLeftOffset < right) {
	// assert decs[initialLeftOffset] > 0;
	// int IndexOfTransitionDecision = searchTransitionDecision(initialLeftOffset, right, decs, nbDecs, depth());
	// if (IndexOfTransitionDecision == -1)
	// right = -1;
	// else {
	// right = IndexOfTransitionDecision;
	// consistent = addTransitionDecisionTo(IndexOfTransitionDecision, tmp, nbFoundTransitionDecisions++, decs, nbDecs);
	// }
	// }
	// restoreProblem();
	// if (consistent && nbFoundTransitionDecisions >= rs.cp.settingLearning.nogoodArityLimit
	// || (right == -1 && nbDecs >= rs.cp.settingLearning.nogoodArityLimit))
	// return null;
	// int[] nogood = null;
	// if (right == -1) {
	// int nbPositiveDecisions = 0;
	// for (int i = 0; i < nbDecs; i++)
	// if (decs[i] > 0)
	// nbPositiveDecisions++;
	// nogood = new int[nbPositiveDecisions + 2];
	// int cnt = 2;
	// for (int i = 0; i < nbDecs; i++)
	// if (decs[i] > 0)
	// nogood[cnt++] = -decs[i];
	// } else {
	// nogood = new int[nbFoundTransitionDecisions + 2];
	// for (int i = 2; i < nogood.length; i++)
	// nogood[i] = -tmp[i - 2];
	// }
	// assert controlMinimalNogood(solver, nogood);
	// return nogood;
	// }
	//
	// public int[] extractMinimalNogoodFrom(SolverBacktrack solver, SetDense denseSet) {
	// return extractMinimalNogoodFrom(solver, denseSet.dense, denseSet.size());
	// }
	//
	// private boolean controlMinimalNogood(SolverBacktrack solver, int[] t) {
	// if (t == null)
	// return true;
	// propagation.queue.clear();
	// // copy of the original problem at depth 0 : it means that all
	// // negative decisions that occur befor the first positive one have
	// // been taken into account
	// for (int i = 0; i < pb.variables.length; i++) {
	// Domain dom = solver.pb.variables[i].dom, auxiliaryDom = pb.variables[i].dom;
	// for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a))
	// if (dom.isRemovedAtLevel(a, 0))
	// auxiliaryDom.remove(a, 0);
	// }
	// boolean notMinimal = false;
	// for (int i = 2; !notMinimal && i < t.length; i++) {
	// int decision = -t[i];
	// Variable x = dr.varIn(decision);
	// int a = dr.idxIn(decision);
	// if (decision > 0) {
	// if (!x.dom.isPresent(a)) {
	// if (i != t.length - 1) {
	// Kit.log.info("nogood not minimal 1 " + x + " " + a);
	// notMinimal = true;
	// }
	// } else {
	// assign(x, a);
	// boolean consistent = propagation.runAfterAssignment(x);
	// if (!consistent && i != t.length - 1) {
	// Kit.log.info("nogood not minimal 2 " + x + " " + a);
	// notMinimal = true;
	// }
	// }
	// } else {
	// if (x.dom.size() == 1 && x.dom.isPresent(a)) {
	// if (i != t.length - 1) {
	// Kit.log.info("nogood not minimal 3 " + x + " " + a);
	// notMinimal = true;
	// }
	// } else if (x.dom.isPresent(a)) {
	// x.dom.removeElementary(a);
	// boolean consistent = x.dom.size() > 0 && propagation.runAfterRefutation(x);
	// if (!consistent && i != t.length - 1) {
	// Kit.log.info("nogood not minimal 4 " + x + " " + a);
	// notMinimal = true;
	// }
	// }
	// }
	// }
	// restoreProblem();
	// return !notMinimal;
	// }
}
