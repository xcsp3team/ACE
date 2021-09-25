/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package learning;

import static utility.Kit.control;

import solver.Solver;
import utility.Bit;
import utility.Enums.Stopping;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class IpsReasonerDominance extends IpsReasoner {

	/**
	 * watches[x][a] is the (head of the) linked list of cells containing IPSs with (x,a) being watched
	 */
	private final WatchCell[] watches;

	/**
	 * The first free cell (i.e. from the pool of free cells)
	 */
	private WatchCell free;

	private final int[] offsets;

	/**
	 * Store for IPSs that must wait for right conditions before entering a watching list
	 */
	private Ips[] quarantine = new Ips[100];

	/**
	 * The number of IPSs in the quarantine store
	 */
	private int quarantineSize;

	private final int[] topBeforeRefutations;

	private final Ips[] waitingNogoods;

	/**
	 * The number of inferred value deletions
	 */
	private int nRemovals;

	/**
	 * The number of inferred wipe-outs
	 */
	private int nWipeouts;

	/**
	 * The number of IPSs
	 */
	private int nIps;

	private static final class WatchCell {

		/**
		 * The IPS recorded in the cell
		 */
		private Ips ips;

		/**
		 * The next cell, following this one, or null
		 */
		private WatchCell next;

		WatchCell(Ips ips, WatchCell next) {
			this.ips = ips;
			this.next = next;
		}
	}

	/**
	 * Builds an object recording IPS and reasoning on them by dominance
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public IpsReasonerDominance(Solver solver) {
		super(solver);
		control(solver.propagation != null);
		int capacity = 0;
		this.offsets = new int[variables.length];
		for (int i = 0; i < offsets.length; i++) {
			offsets[i] = capacity;
			capacity += variables[i].dom.initSize();
		}
		this.watches = new WatchCell[capacity];
		if (extractor.enablePElimination()) {
			this.topBeforeRefutations = new int[variables.length + 1];
			this.waitingNogoods = null;
		} else {
			this.topBeforeRefutations = null;
			this.waitingNogoods = new Ips[variables.length + 1];
		}
	}

	private void insertIps(Ips ips, int accessKey) {
		if (free == null)
			watches[accessKey] = new WatchCell(ips, watches[accessKey]);
		else {
			WatchCell cell = free;
			free = free.next;
			cell.ips = ips;
			cell.next = watches[accessKey];
			watches[accessKey] = cell;
		}
	}

	private boolean canFindAnotherWatch(Ips ips, int watchPosition) {
		int pos = ips.watchPosFor(watchPosition);
		Variable x = ips.vars[pos];
		int a = Bit.firstPositionOfNonInclusion(x.dom.binary(), ips.doms[pos]);
		if (a != -1) {
			insertIps(ips, offsets[x.num] + a);
			ips.setIndex(watchPosition, a);
			return true;
		}
		for (int i = 0; i < ips.size(); i++) {
			Variable y = ips.vars[i];
			if (ips.isWatched(y))
				continue;
			a = Bit.firstPositionOfNonInclusion(y.dom.binary(), ips.doms[i]);
			if (a != -1) {
				insertIps(ips, offsets[y.num] + a);
				ips.setWatch(watchPosition, i, a); // indexPosition);addWatch(ips, watchPosition, i, &);
				return true;
			}
		}
		return false;
	}

	public boolean checkWatchesOf(Variable x, int a) {
		int lit = offsets[x.num] + a;
		WatchCell previous = null, current = watches[lit];
		while (current != null) {
			Ips ips = current.ips;
			int watch = ips.watchFor(x); // watch is 0 or 1 (first or second watch)
			if (canFindAnotherWatch(ips, watch)) {
				WatchCell tmp = current.next;
				if (previous == null)
					watches[lit] = current.next;
				else
					previous.next = current.next;
				current.next = free;
				free = current;
				current = tmp;
			} else {
				previous = current;
				current = current.next;
				if (!dealWithInference(ips, ips.watchPosFor(watch == 0 ? 1 : 0)))
					return false;
			}
		}
		return true;
	}

	private boolean canFindAWatch(Ips ips, int discardedPosition) {
		for (int i = 0; i < ips.size(); i++) {
			if (i == discardedPosition)
				continue;
			int a = Bit.firstPositionOfNonInclusion(ips.vars[i].dom.binary(), ips.doms[i]);
			if (a != -1) {
				ips.setWatch(discardedPosition == -1 ? 0 : 1, i, a);
				return true;
			}
		}
		return false;
	}

	private boolean dealWithInference(Ips ips, int pos) {
		Variable x = ips.vars[pos];
		long[] set = ips.doms[pos];
		Domain dom = x.dom;
		if (x.assigned() && Bit.isPresent(set, dom.first())) {
			if (solver.proofer != null)
				solver.proofer.updateProof(ips.vars);
			nWipeouts++;
			return false;
		}

		int sizeBefore = dom.size();
		for (int a = dom.first(); a != -1; a = dom.next(a))
			if (Bit.isPresent(set, a))
				dom.removeElementary(a);
		int nRemovals = sizeBefore - dom.size();
		if (nRemovals > 0) {
			if (solver.proofer != null)
				solver.proofer.updateProof(ips.vars);
			if (dom.size() == 0)
				nWipeouts++;
			else
				nRemovals += nRemovals;
			if (dom.afterElementaryCalls(sizeBefore) == false)
				return false;
		}
		return true;
	}

	private boolean manageQuarantine() {
		for (int i = 0; i < quarantineSize; i++) {
			Ips ips = quarantine[i];
			if (ips.size() == 1) {
				if (!dealWithInference(ips, 0))
					return false;
			} else {
				if (!canFindAWatch(ips, -1)) {
					if (solver.proofer != null)
						solver.proofer.updateProof(ips.vars);
					nWipeouts++;
					return false;
				}
				int pos = ips.watchPosFor(0);
				if (canFindAWatch(ips, pos)) {
					insertIps(ips, offsets[ips.varNumFor(0)] + ips.watchIdxFor(0));
					insertIps(ips, offsets[ips.varNumFor(1)] + ips.watchIdxFor(1));
					quarantineSize--;
					quarantine[i--] = quarantine[quarantineSize];
					nIps++;
				} else {
					if (!dealWithInference(ips, pos))
						return false;
				}
			}
		}
		return true;
	}

	private void preparePartialBacktrack(int depth) {
		int top = solver.stackedVariables.top;
		Variable[] stack = solver.stackedVariables.stack;
		topBeforeRefutations[depth] = top;
		if (top == -1 || stack[top].dom.lastRemovedLevel() < depth)
			return;
		for (int i = top; stack[i] != null; i--)
			stack[i].dom.setMark(depth); // getLastDropped();
	}

	@Override
	public boolean whenOpeningNode() {
		if (extractor.enablePElimination())
			topBeforeRefutations[solver.depth()] = -2;
		if (manageQuarantine() == false || solver.propagation.propagate() == false)
			return false;
		if (extractor.enablePElimination()) {
			preparePartialBacktrack(solver.depth());
			// waitingNogoods[solver.getCurrentDepth()] = new Ips(solver, reductionOperator.copy());
		} else
			waitingNogoods[solver.depth()] = new Ips(extractor.extract());
		return true;
	}

	private void performPartialBacktrack(int topBefore, int depth) {
		int top = solver.stackedVariables.top;
		Variable[] stack = solver.stackedVariables.stack;
		// Possible d'eliminer ci-dessous : semble pas possible ces cas ? //TODO
		if (top == -1 || stack[top].dom.lastRemovedLevel() < depth)
			return;
		solver.stackedVariables.top = topBefore; // keep it at this position
		for (int i = top; i > topBefore; i--) {
			if (stack[i] == null) {
				assert (i == topBefore + 1);
				return;
			}
			stack[i].dom.restoreBefore(depth);
		}
		for (int i = topBefore; stack[i] != null; i--)
			stack[i].dom.restoreAtMark(depth); // restoreElementsDroppedStrictlyAfter(currentFrontiers[cnt]);
	}

	@Override
	public void whenClosingNode() {
		int depth = solver.depth();
		if (depth == 0)
			return;
		Ips ips = null;
		if (extractor.enablePElimination()) {
			int topBefore = topBeforeRefutations[depth];
			if (topBefore == -2)
				return;
			performPartialBacktrack(topBefore, depth);
			ips = new Ips(extractor.extract());
			// ips = new Ips(solver, ((SystematicSolver) solver).getProofVariablesAt(solver.getCurrentDepth()));
			// ips = new Ips(waitingNogoods[level],
			// ((SystematicSolver)solver).getProofVariablesAt(solver.getCurrentDepth() ));
		} else
			ips = waitingNogoods[depth];
		assert ips != null;
		if (ips.size() == 0) {
			Kit.log.info("empty nogood");
			solver.stopping = Stopping.FULL_EXPLORATION;
		} else {
			if (quarantineSize + 1 > quarantine.length) {
				Ips[] t = new Ips[quarantine.length * 2];
				System.arraycopy(quarantine, 0, t, 0, quarantine.length);
				quarantine = t;
			}
			quarantine[quarantineSize++] = ips;
		}
	}

	@Override
	public void displayStats() {
		Kit.log.info("nIPSs" + nIps + " nRemovals=" + nRemovals + " nWipeouts=" + nWipeouts);
	}

	public void display() {
		Kit.log.fine("nIPSs = " + nIps);
		for (int i = 0; i < watches.length; i++) {
			String s = "Watches for " + solver.problem.variables[i] + " ";
			for (WatchCell cell = watches[i]; cell != null; cell = cell.next)
				s += cell.ips.toString();
			Kit.log.fine(s);
		}
	}

}

// int topStack = solver.getTopStack();
// Variable[] globalStack = solver.getGlobalStack();
//
// if (topStack == -1 || globalStack[topStack].domain.getElements().getLastAbsentLevel() < level)
// return;
//
// solver.setTopStack(topBefore); // keep it at this position
//
// for (int i = topStack; i > topBefore; i--) {
// if (globalStack[i] == Variable.TAG) {
// if (i != topBefore + 1)
// Kit.prn("i = " + i + " top = " + topBefore);
// return;
// }
// globalStack[i].domain.getElements().restoreElementsAtLevelGreaterThanOrEqualTo(level);
// }
//
// // solver.setTopStack(topBefore); // keep it at this position
//
// int[] currentFrontiers = frontiers[level];
// int i = 0;
// int j = topBefore;
// while (currentFrontiers[i] != -1) {
// globalStack[j].domain.getElements().restoreElementsRemovedStrictlyAfter(currentFrontiers[i]);
// j--;
// i++;
// }

// int cnt = 0;

// for (int i = topBefore, cnt=0; globalStack[i] != Variable.TAG; i--, cnt++)
// globalStack[i].domain.getElements().restoreElementsRemovedStrictlyAfter(currentFrontiers[cnt]);

// solver.setTopStack(topBefore);

// for (int i = topStack; i > topBefore; i--) {
// if (globalStack[i] == Variable.TAG)
// break;
// globalStack[i].domain.getElements().restoreElementsAtLevelGreaterThanOrEqualTo(level);
// }
//
// solver.setTopStack(topBefore);
//
// int[] currentFrontiers = frontiers[level];
// int i = 0;
// int j = topBefore;
// while (currentFrontiers[i] != -1) {
// globalStack[j].domain.getElements().restoreElementsRemovedStrictlyAfter(currentFrontiers[i]);
// j--;
// i++;
// }
