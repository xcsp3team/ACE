/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package learning;

import interfaces.ObserverBacktracking.ObserverBacktrackingUnsystematic;
import search.backtrack.SolverBacktrack;
import search.backtrack.SolverBacktrack.GlobalObserver;
import utility.Enums.EStopping;
import utility.Kit;
import utility.operations.Bit;
import variables.Variable;
import variables.domains.Domain;

public final class LearnerStatesDominance extends LearnerStates {
	protected State[] waitingNogoods;

	protected WatchCell[] watches; // 1D = variable id ; value = reference to the first cell involving the variable as watch in a
									// hypernogood

	protected WatchCell free; // reference to the first free cell (i.e. the pool of free cells)

	protected int nbTotalRemovals, nbWipeout, nbHyperNogoods;

	public int nbGeneratedHyperNogoods;

	private int[] offsets;

	private State[] quarantine = new State[100];

	private int quarantineSize;

	private int[] topBeforeRefutations;

	// private int[][] frontiers;

	class WatchCell {
		State state;

		WatchCell nextCell;

		WatchCell(State state, WatchCell nextCell) {
			this.state = state;
			this.nextCell = nextCell;
		}
	}

	public LearnerStatesDominance(SolverBacktrack solver) {
		super(solver);
		Kit.control(solver.propagation != null);

		int capacity = 0;
		offsets = new int[solver.pb.variables.length];
		for (int i = 0; i < offsets.length; i++) {
			offsets[i] = capacity;
			capacity += solver.pb.variables[i].dom.initSize();
		}
		watches = new WatchCell[capacity];
		if (reductionOperator.enablePElimination())
			topBeforeRefutations = new int[offsets.length + 1]; // offsets.length is equal to the nb of variables
		else
			waitingNogoods = new State[offsets.length + 1];

		solver.propagation.queue.setStateDominanceManager(this);
	}

	private void insertHyperNogood(State hyperNogood, int accessKey) {
		if (free == null)
			watches[accessKey] = new WatchCell(hyperNogood, watches[accessKey]);
		else {
			WatchCell cell = free;
			free = free.nextCell;
			cell.state = hyperNogood;
			cell.nextCell = watches[accessKey];
			watches[accessKey] = cell;
		}
	}

	private boolean canFindAnotherWatch(State hyperNogood, int watchPosition) {
		long[] binDom = variables[hyperNogood.getVariableIdWatchedAt(watchPosition)].dom.binaryRepresentation();
		int pos = Bit.firstPositionOfNonInclusion(binDom, hyperNogood.getDomainRepresentationOfWatchedVariableAt(watchPosition));
		if (pos != -1) {
			insertHyperNogood(hyperNogood, offsets[hyperNogood.getVariableIdWatchedAt(watchPosition)] + pos);
			hyperNogood.setIndex(watchPosition, pos);
			return true;
		}

		int[] vids = hyperNogood.vids;
		for (int i = 0; i < vids.length; i++) {
			if (hyperNogood.isWatched(vids[i]))
				continue;
			binDom = variables[vids[i]].dom.binaryRepresentation();
			pos = Bit.firstPositionOfNonInclusion(binDom, hyperNogood.getDomainRepresentationOfVariableAtPosition(i));
			if (pos != -1) {
				insertHyperNogood(hyperNogood, offsets[vids[i]] + pos);
				hyperNogood.setWatch(watchPosition, i, pos); // indexPosition);addWatch(hyperNogood, watchPosition, i, pos);
				return true;
			}
		}
		return false;
	}

	public boolean checkWatchesOf(int vid, int idx) {
		int lit = offsets[vid] + idx;
		WatchCell previous = null;
		WatchCell current = watches[lit];
		while (current != null) {
			State hyperNogood = current.state;
			int watchPosition = hyperNogood.getWatchPositionOf(vid);
			if (canFindAnotherWatch(hyperNogood, watchPosition)) {
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
				if (!dealWithInference(hyperNogood, hyperNogood.getVariablePositionAt(watchPosition == 0 ? 1 : 0)))
					return false;
			}
		}
		return true;
	}

	private boolean canFindAWatch(State hyperNogood, int pos) {
		int[] vids = hyperNogood.vids;
		for (int i = 0; i < vids.length; i++) {
			if (i == pos)
				continue;
			long[] binDom = variables[vids[i]].dom.binaryRepresentation();
			int indexPosition = Bit.firstPositionOfNonInclusion(binDom, hyperNogood.getDomainRepresentationOfVariableAtPosition(i));
			if (indexPosition != -1) {
				hyperNogood.setWatch(pos == -1 ? 0 : 1, i, indexPosition);
				return true;
			}
		}
		return false;
	}

	protected boolean dealWithInference(State hyperNogood, int pos) {
		Variable var = solver.pb.variables[hyperNogood.vids[pos]];
		long[] domainRepresentation = hyperNogood.getDomainRepresentationAt(pos);
		Domain dom = var.dom;
		if (var.isAssigned() && Bit.isPresent(domainRepresentation, dom.first())) {
			solver.proofer.updateProof(hyperNogood.vids);
			nbWipeout++;
			return false;
		}

		int sizeBefore = dom.size();
		for (int idx = dom.first(); idx != -1; idx = dom.next(idx))
			if (Bit.isPresent(domainRepresentation, idx))
				dom.removeElementary(idx);
		int nbRemovals = sizeBefore - dom.size();
		if (nbRemovals > 0) {
			solver.proofer.updateProof(hyperNogood.vids);
			if (dom.size() == 0)
				nbWipeout++;
			else
				nbTotalRemovals += nbRemovals;
			if (dom.afterElementaryCalls(sizeBefore) == false)
				return false;
		}
		return true;
	}

	private boolean manageQuarantine() {
		for (int i = 0; i < quarantineSize; i++) {
			State hyperNogood = quarantine[i];
			int[] vids = hyperNogood.vids;
			if (vids.length == 1) {
				if (!dealWithInference(hyperNogood, 0))
					return false;
			} else {
				if (!canFindAWatch(hyperNogood, -1)) {
					solver.proofer.updateProof(hyperNogood.vids);
					nbWipeout++;
					return false;
				}
				int pos = hyperNogood.getVariablePositionAt(0);
				if (canFindAWatch(hyperNogood, pos)) {
					insertHyperNogood(hyperNogood, offsets[hyperNogood.getVariableIdWatchedAt(0)] + hyperNogood.getIndexWatchedAt(0));
					insertHyperNogood(hyperNogood, offsets[hyperNogood.getVariableIdWatchedAt(1)] + hyperNogood.getIndexWatchedAt(1));
					quarantineSize--;
					quarantine[i--] = quarantine[quarantineSize];
					nbHyperNogoods++;
				} else {
					if (!dealWithInference(hyperNogood, pos))
						return false;
				}
			}
		}
		return true;
	}

	private void preparePartialBacktrack(int level) {
		GlobalObserver variablesObserver = solver.observerVars;
		int topStack = variablesObserver.top;
		ObserverBacktrackingUnsystematic[] globalStack = variablesObserver.stack;
		topBeforeRefutations[level] = topStack;
		if (topStack == -1 || ((Variable) globalStack[topStack]).dom.lastRemovedLevel() < level)
			return;
		for (int i = topStack; globalStack[i] != null; i--)
			((Variable) globalStack[i]).dom.setMark(level); // getLastDropped();
	}

	@Override
	public boolean dealWhenOpeningNode() {
		if (reductionOperator.enablePElimination())
			topBeforeRefutations[solver.depth()] = -2;
		if (!manageQuarantine() || !solver.propagation.propagate())
			return false;
		if (reductionOperator.enablePElimination()) {
			preparePartialBacktrack(solver.depth());
			// waitingNogoods[solver.getCurrentDepth()] = new HyperNogood(solver, reductionOperator.copy());
		} else
			waitingNogoods[solver.depth()] = new State(this, reductionOperator.extract());
		return true;
	}

	private void performPartialBacktrack(int topBefore, int depth) {
		GlobalObserver variablesObserver = solver.observerVars;
		int topStack = variablesObserver.top;
		ObserverBacktrackingUnsystematic[] globalStack = variablesObserver.stack;
		// Possible d'eliminer ci-dessous : semble pas possible ces cas ? //TODO
		if (topStack == -1 || ((Variable) globalStack[topStack]).dom.lastRemovedLevel() < depth)
			return;
		variablesObserver.top = topBefore; // keep it at this position
		for (int i = topStack; i > topBefore; i--) {
			if (globalStack[i] == null) {
				assert (i == topBefore + 1);
				return;
			}
			((Variable) globalStack[i]).dom.restoreBefore(depth);
		}
		// int[] currentFrontiers = frontiers[level];
		for (int i = topBefore; globalStack[i] != null; i--)
			((Variable) globalStack[i]).dom.restoreAtMark(depth); // restoreElementsDroppedStrictlyAfter(currentFrontiers[cnt]);
	}

	@Override
	public void dealWhenClosingNode() {
		int level = solver.depth();
		if (level == 0)
			return;
		State state = null;
		if (reductionOperator.enablePElimination()) {
			int topBefore = topBeforeRefutations[level];
			if (topBefore == -2)
				return;
			performPartialBacktrack(topBefore, level);
			state = new State(this, reductionOperator.extract());
			// // hyperNogood = new HyperNogood(solver, ((SystematicSolver)
			// solver).getProofVariablesAt(solver.getCurrentDepth()));

			// hyperNogood = new HyperNogood(waitingNogoods[level], ((SystematicSolver)
			// solver).getProofVariablesAt(solver.getCurrentDepth() ));
		} else
			state = waitingNogoods[level];
		assert state != null;
		if (state.vids.length == 0) {
			Kit.log.info("empty nogood");
			solver.stoppingType = EStopping.FULL_EXPLORATION;
		} else {
			if (quarantineSize + 1 > quarantine.length) {
				State[] t = new State[quarantine.length * 2];
				System.arraycopy(quarantine, 0, t, 0, quarantine.length);
				quarantine = t;
			}
			quarantine[quarantineSize++] = state;
		}
	}

	@Override
	public void displayStats() {
		Kit.log.info("nbHyperNogoods=" + nbGeneratedHyperNogoods + " nbTotalRemovals=" + nbTotalRemovals + " nbWipeouts=" + nbWipeout);
	}

	public void display() {
		Kit.log.fine("Nb Hyper Nogoods = " + nbHyperNogoods);
		for (int i = 0; i < watches.length; i++) {
			String s = "Watches for " + solver.pb.variables[i] + " ";
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
