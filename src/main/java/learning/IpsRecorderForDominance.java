/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package learning;

import solver.Solver;
import utility.Bit;
import utility.Enums.EStopping;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class IpsRecorderForDominance extends IpsRecorder {
	protected Ips[] waitingNogoods;

	protected WatchCell[] watches; // 1D = variable id ; value = reference to the first cell involving the variable as watch in a
									// hypernogood

	protected WatchCell free; // reference to the first free cell (i.e. the pool of free cells)

	protected int nTotalRemovals, nWipeouts, nIps;

	public int nGeneratedIps;

	private int[] offsets;

	private Ips[] quarantine = new Ips[100];

	private int quarantineSize;

	private int[] topBeforeRefutations;

	// private int[][] frontiers;

	class WatchCell {
		Ips state;

		WatchCell nextCell;

		WatchCell(Ips state, WatchCell nextCell) {
			this.state = state;
			this.nextCell = nextCell;
		}
	}

	public IpsRecorderForDominance(Solver solver) {
		super(solver);
		Kit.control(solver.propagation != null);

		int capacity = 0;
		offsets = new int[variables.length];
		for (int i = 0; i < offsets.length; i++) {
			offsets[i] = capacity;
			capacity += variables[i].dom.initSize();
		}
		watches = new WatchCell[capacity];
		if (reductionOperator.enablePElimination())
			topBeforeRefutations = new int[offsets.length + 1]; // offsets.length is equal to the nb of variables
		else
			waitingNogoods = new Ips[offsets.length + 1];

		solver.propagation.queue.setStateDominanceManager(this);
	}

	private void insertIps(Ips ips, int accessKey) {
		if (free == null)
			watches[accessKey] = new WatchCell(ips, watches[accessKey]);
		else {
			WatchCell cell = free;
			free = free.nextCell;
			cell.state = ips;
			cell.nextCell = watches[accessKey];
			watches[accessKey] = cell;
		}
	}

	private boolean canFindAnotherWatch(Ips ips, int watchPosition) {
		int x = ips.varNumFor(watchPosition);
		long[] binDom = variables[x].dom.binary();
		int a = Bit.firstPositionOfNonInclusion(binDom, ips.binDomFor(watchPosition));
		if (a != -1) {
			insertIps(ips, offsets[x] + a);
			ips.setIndex(watchPosition, a);
			return true;
		}
		for (int i = 0; i < ips.nums.length; i++) {
			int y = ips.nums[i];
			if (ips.isWatched(y))
				continue;
			binDom = variables[y].dom.binary();
			a = Bit.firstPositionOfNonInclusion(binDom, ips.binDoms[i]);
			if (a != -1) {
				insertIps(ips, offsets[y] + a);
				ips.setWatch(watchPosition, i, a); // indexPosition);addWatch(ips, watchPosition, i, &);
				return true;
			}
		}
		return false;
	}

	public boolean checkWatchesOf(int x, int a) {
		int lit = offsets[x] + a;
		WatchCell previous = null;
		WatchCell current = watches[lit];
		while (current != null) {
			Ips ips = current.state;
			int watch = ips.watchFor(x); // watch is 0 or 1 (first or second watch)
			if (canFindAnotherWatch(ips, watch)) {
				WatchCell tmp = current.nextCell;
				if (previous == null)
					watches[lit] = current.nextCell;
				else
					previous.nextCell = current.nextCell;
				current.nextCell = free;
				free = current;
				current = tmp;
			} else {
				previous = current;
				current = current.nextCell;
				if (!dealWithInference(ips, ips.watchVarFor(watch == 0 ? 1 : 0)))
					return false;
			}
		}
		return true;
	}

	private boolean canFindAWatch(Ips ips, int pos) {
		int[] nums = ips.nums;
		for (int i = 0; i < nums.length; i++) {
			if (i == pos)
				continue;
			long[] binDom = variables[nums[i]].dom.binary();
			int a = Bit.firstPositionOfNonInclusion(binDom, ips.binDoms[i]);
			if (a != -1) {
				ips.setWatch(pos == -1 ? 0 : 1, i, a);
				return true;
			}
		}
		return false;
	}

	protected boolean dealWithInference(Ips ips, int pos) {
		Variable x = variables[ips.nums[pos]];
		long[] domainRepresentation = ips.binDoms[pos];
		Domain dom = x.dom;
		if (x.assigned() && Bit.isPresent(domainRepresentation, dom.first())) {
			solver.proofer.updateProof(ips.nums);
			nWipeouts++;
			return false;
		}

		int sizeBefore = dom.size();
		for (int a = dom.first(); a != -1; a = dom.next(a))
			if (Bit.isPresent(domainRepresentation, a))
				dom.removeElementary(a);
		int nRemovals = sizeBefore - dom.size();
		if (nRemovals > 0) {
			solver.proofer.updateProof(ips.nums);
			if (dom.size() == 0)
				nWipeouts++;
			else
				nTotalRemovals += nRemovals;
			if (dom.afterElementaryCalls(sizeBefore) == false)
				return false;
		}
		return true;
	}

	private boolean manageQuarantine() {
		for (int i = 0; i < quarantineSize; i++) {
			Ips ips = quarantine[i];
			int[] nums = ips.nums;
			if (nums.length == 1) {
				if (!dealWithInference(ips, 0))
					return false;
			} else {
				if (!canFindAWatch(ips, -1)) {
					solver.proofer.updateProof(ips.nums);
					nWipeouts++;
					return false;
				}
				int pos = ips.watchVarFor(0);
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

	private void preparePartialBacktrack(int level) {
		int top = solver.stackedVariables.top;
		Variable[] stack = solver.stackedVariables.stack;
		topBeforeRefutations[level] = top;
		if (top == -1 || ((Variable) stack[top]).dom.lastRemovedLevel() < level)
			return;
		for (int i = top; stack[i] != null; i--)
			((Variable) stack[i]).dom.setMark(level); // getLastDropped();
	}

	@Override
	public boolean dealWhenOpeningNode() {
		if (reductionOperator.enablePElimination())
			topBeforeRefutations[solver.depth()] = -2;
		if (!manageQuarantine() || !solver.propagation.propagate())
			return false;
		if (reductionOperator.enablePElimination()) {
			preparePartialBacktrack(solver.depth());
			// waitingNogoods[solver.getCurrentDepth()] = new Ips(solver, reductionOperator.copy());
		} else
			waitingNogoods[solver.depth()] = new Ips(this, reductionOperator.extract());
		return true;
	}

	private void performPartialBacktrack(int topBefore, int depth) {
		int top = solver.stackedVariables.top;
		Variable[] stack = solver.stackedVariables.stack;
		// Possible d'eliminer ci-dessous : semble pas possible ces cas ? //TODO
		if (top == -1 || ((Variable) stack[top]).dom.lastRemovedLevel() < depth)
			return;
		solver.stackedVariables.top = topBefore; // keep it at this position
		for (int i = top; i > topBefore; i--) {
			if (stack[i] == null) {
				assert (i == topBefore + 1);
				return;
			}
			((Variable) stack[i]).dom.restoreBefore(depth);
		}
		// int[] currentFrontiers = frontiers[level];
		for (int i = topBefore; stack[i] != null; i--)
			((Variable) stack[i]).dom.restoreAtMark(depth); // restoreElementsDroppedStrictlyAfter(currentFrontiers[cnt]);
	}

	@Override
	public void dealWhenClosingNode() {
		int level = solver.depth();
		if (level == 0)
			return;
		Ips ips = null;
		if (reductionOperator.enablePElimination()) {
			int topBefore = topBeforeRefutations[level];
			if (topBefore == -2)
				return;
			performPartialBacktrack(topBefore, level);
			ips = new Ips(this, reductionOperator.extract());
			// ips = new Ips(solver, ((SystematicSolver) solver).getProofVariablesAt(solver.getCurrentDepth()));
			// ips = new Ips(waitingNogoods[level], ((SystematicSolver)solver).getProofVariablesAt(solver.getCurrentDepth() ));
		} else
			ips = waitingNogoods[level];
		assert ips != null;
		if (ips.nums.length == 0) {
			Kit.log.info("empty nogood");
			solver.stopping = EStopping.FULL_EXPLORATION;
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
		Kit.log.info("nIps=" + nGeneratedIps + " nTotalRemovals=" + nTotalRemovals + " nWipeouts=" + nWipeouts);
	}

	public void display() {
		Kit.log.fine("nIps = " + nIps);
		for (int i = 0; i < watches.length; i++) {
			String s = "Watches for " + solver.problem.variables[i] + " ";
			for (WatchCell cell = watches[i]; cell != null; cell = cell.nextCell)
				s += cell.state.toString();
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
