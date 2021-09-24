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

import java.util.stream.IntStream;
import java.util.stream.Stream;

import dashboard.Control.SettingLearning;
import solver.Decisions;
import solver.Solver;
import utility.Enums.LearningNogood;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class NogoodRecorder {

	public static NogoodRecorder buildFor(Solver solver) {
		if (solver.head.control.solving.enableSearch && solver.head.control.learning.nogood != LearningNogood.NO && solver.propagation.queue != null)
			return new NogoodRecorder(solver);
		return null;
	}

	public boolean checkIndexes(int[] t) {
		// note that nogoods are stored with indexes of values
		extern: for (int i = 0; i < nNogoods; i++) {
			for (int d : nogoods[i].literals) {
				int x = decisions.numIn(d);
				int a = decisions.idxIn(d);
				if (t[x] != a)
					continue extern;
			}
			return false;
		}
		return true;
	}

	private static final class WatchCell {

		private Nogood nogood;

		private WatchCell nextCell;

		private WatchCell(Nogood nogood, WatchCell nextCell) {
			this.nogood = nogood;
			this.nextCell = nextCell;
		}
	}

	public final Solver solver;

	final Decisions decisions; // redundant field

	final SettingLearning settings;

	Nogood[] nogoods;

	public int nNogoods;

	private final WatchCell[][] pws; // positive watch lists; pws[x][a] is the first cell (so, nogood) involving the
										// positive literal (x=a) as being watched

	private final WatchCell[][] nws; // negative watch lists; nws[x][a] is the first cell (nogood) involving the
										// negative literal (x!=a) as being watched

	private WatchCell free; // reference to the first free cell (i.e. the pool of free cells)

	// public final SymmetryHandler symmetryHandler;

	private int[] tmp;

	public void reset() {
		nNogoods = 0;
		Kit.fill(pws, null); // TODO put them in free instead
		Kit.fill(nws, null); // TODO put them in free instead
		// Kit.control(symmetryHandler == null);
	}

	public NogoodRecorder(Solver solver) {
		this.solver = solver;
		this.decisions = solver.decisions;
		this.settings = solver.head.control.learning;
		this.nogoods = new Nogood[settings.nogoodBaseLimit];
		this.pws = Stream.of(solver.problem.variables).map(x -> new WatchCell[x.dom.initSize()]).toArray(WatchCell[][]::new);
		this.nws = Stream.of(solver.problem.variables).map(x -> new WatchCell[x.dom.initSize()]).toArray(WatchCell[][]::new);
		this.tmp = new int[solver.problem.variables.length];
		// symmetryHandler = settings.nogood == RST_SYM ? new SymmetryHandler(this,problem.variables.length) : null;
	}

	/**********************************************************************************************
	 * About filtering
	 *********************************************************************************************/

	private boolean canBeWatched(int decision) {
		assert decision != 0;
		Variable x = decisions.varIn(decision);
		int a = decisions.idxIn(decision);
		return decision > 0 ? x.dom.contains(a) : x.dom.size() > 1 || !x.dom.contains(a);
	}

	private boolean canFindAnotherWatchFor(Nogood nogood, boolean firstWatch) {
		int[] decs = nogood.literals;
		int start = nogood.getWatchedPosition(firstWatch);
		for (int i = start + 1; i < decs.length; i++)
			if (!nogood.isPositionWatched(i) && canBeWatched(decs[i])) {
				addWatchFor(nogood, i, firstWatch);
				return true;
			}
		for (int i = 0; i < start; i++)
			if (!nogood.isPositionWatched(i) && canBeWatched(decs[i])) {
				addWatchFor(nogood, i, firstWatch);
				return true;
			}
		return false;
	}

	private boolean dealWithInference(int inferenceDecision) {
		Variable x = decisions.varIn(inferenceDecision);
		int a = decisions.idxIn(inferenceDecision);
		solver.propagation.currFilteringCtr = null;
		Domain dom = x.dom;
		if (inferenceDecision > 0)
			return dom.reduceTo(a);
		return dom.removeIfPresent(a);
	}

	private boolean checkWatchesOf(WatchCell[] watchCells, int a, int watchedDecision) {
		WatchCell previous = null, current = watchCells[a];
		while (current != null) {
			Nogood nogood = current.nogood;
			int watchedDecision2 = nogood.getSecondWatchedDecision(watchedDecision);
			if (!decisions.varIn(watchedDecision2).dom.contains(decisions.idxIn(watchedDecision2))) {
				previous = current;
				current = current.nextCell;
			} else if (canFindAnotherWatchFor(nogood, nogood.isDecisionWatchedByFirstWatch(watchedDecision))) {
				WatchCell tmp = current.nextCell;
				if (previous == null)
					watchCells[a] = current.nextCell;
				else
					previous.nextCell = current.nextCell;
				current.nextCell = free;
				free = current;
				current = tmp;
			} else {
				previous = current;
				current = current.nextCell;
				if (!dealWithInference(nogood.getSecondWatchedDecision(watchedDecision)))
					return false;
			}
		}
		assert controlWatches();
		return true;
	}

	public boolean checkWatchesOf(Variable x, int a, boolean positive) {
		return positive ? checkWatchesOf(pws[x.num], a, decisions.positiveDecisionFor(x.num, a))
				: checkWatchesOf(nws[x.num], a, decisions.negativeDecisionFor(x.num, a));
	}

	public boolean runPropagator(Variable x) {
		if (x.dom.size() == 1 && checkWatchesOf(x, x.dom.first(), false) == false)
			return false;
		return true;
	}

	/**********************************************************************************************
	 * About recording
	 *********************************************************************************************/

	private void addWatchFor(Nogood nogood, int position, boolean firstWatch) {
		int decision = nogood.literals[position];
		WatchCell[] cells = decision > 0 ? pws[decisions.numIn(decision)] : nws[decisions.numIn(decision)];
		int a = decisions.idxIn(decision);
		if (free == null)
			cells[a] = new WatchCell(nogood, cells[a]);
		else {
			WatchCell cell = free;
			free = free.nextCell;
			cell.nogood = nogood;
			cell.nextCell = cells[a];
			cells[a] = cell;
		}
		nogood.setWatchedPosition(position, firstWatch);
	}

	public void addNogood(int[] decs, boolean toBeSorted) {
		if (nNogoods < nogoods.length) {
			decs = toBeSorted ? Kit.sort(decs) : decs;
			Nogood nogood = nogoods[nNogoods++] = new Nogood(decs);
			addWatchFor(nogood, decs.length - 2, true);
			addWatchFor(nogood, decs.length - 1, false);
			// if (symmetryHandler != null) symmetryHandler.addNogood(decs);
		}
	}

	public void addNogoodsOfCurrentBranch() {
		if (!settings.nogood.isRstType() || decisions.set.size() < 2)
			return;
		int nMetPositiveDecisions = 0;
		for (int i = 0; i <= decisions.set.limit; i++) {
			int d = decisions.set.dense[i];
			if (d > 0)
				tmp[nMetPositiveDecisions++] = d;
			else if (nMetPositiveDecisions > 0) {
				int[] currentNogood = new int[nMetPositiveDecisions + 1];
				if (settings.nogood == LearningNogood.RST_MIN && decisions.isFailedAssignment(i)) {
					boolean bottomUp = true; // hard coding TODO
					if (bottomUp)
						for (int j = 0; j < nMetPositiveDecisions; j++)
							currentNogood[j] = tmp[nMetPositiveDecisions - j - 1];
					else
						for (int j = 0; j < nMetPositiveDecisions; j++)
							currentNogood[j] = tmp[j];
					currentNogood[currentNogood.length - 1] = -d;
					int[] minimizedNogood = solver.nogoodMinimizer.extractMinimalNogoodFrom(currentNogood);
					if (minimizedNogood != null) {
						if (minimizedNogood.length == 0) {
							Kit.log.fine("Empty nogood => Inconistency");
							return; // inconsistency proved
						}
						addNogood(minimizedNogood, false); // symmetryHandler != null);
					}
				} else { // if (dr.isFailedAssignment(i)){
							// record negative decisions for direct insertion of the nogod
					for (int j = 0; j < nMetPositiveDecisions; j++)
						currentNogood[j] = -tmp[j];
					currentNogood[nMetPositiveDecisions] = d;
					addNogood(currentNogood, false); // symmetryHandler != null);
				}
				// if (symmetryHandler != null) symmetryHandler.handleSymmetricNaryNogoods(currentNogood);
			}
			// else if (symmetryHandler != null) symmetryHandler.handleSymmetricUnaryNogoods(d);
		}
		// display();
		assert controlWatches();
	}

	private boolean control(WatchCell[][] watches, boolean positive) {
		for (int i = 0; i < watches.length; i++)
			for (int j = 0; j < watches[i].length; j++)
				for (WatchCell cell = watches[i][j]; cell != null; cell = cell.nextCell)
					if (!cell.nogood.isDecisionWatched(positive ? decisions.positiveDecisionFor(i, j) : decisions.negativeDecisionFor(i, j))) {
						Kit.log.warning("nogood = " + cell.nogood + " does not watch");
						return false;
					}
		return true;
	}

	private boolean controlNogood(int wdec, Nogood nogood) {
		WatchCell firstCell = wdec > 0 ? pws[decisions.numIn(wdec)][decisions.idxIn(wdec)] : nws[decisions.numIn(wdec)][decisions.idxIn(wdec)];
		for (WatchCell cell = firstCell; cell != null; cell = cell.nextCell)
			if (cell.nogood == nogood)
				return true;
		return false;
	}

	protected boolean controlWatches() {
		if (!control(pws, true) || !control(nws, false))
			return false;
		for (int i = 0; i < nNogoods; i++)
			if (nogoods[i] != null
					&& (!controlNogood(nogoods[i].getWatchedDecision(true), nogoods[i]) || !controlNogood(nogoods[i].getWatchedDecision(false), nogoods[i])))
				return false;
		return true;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder("Nogoods = {\n");
		IntStream.range(0, nNogoods).forEach(i -> sb.append(nogoods[i].toString(decisions)).append("\n"));
		return sb.append("}").toString();
	}

}

// public void addNogoodFrom(int[] decs) {
// addNogood(decs, true);
// }

// private int[] copy(SetDense denseSet, int coefficient) {
// int[] dst = new int[denseSet.size()];
// int[] dense = denseSet.dense;
// for (int i = dst.length - 1; i >= 0; i--)
// dst[i] = coefficient * dense[i];
// return dst;
// }

// public void addCurrentNogood() {
// // the second part of the test below corresponds to the fact a nogood
// // with only one positive decision is recorded via the removal of a value at depth 0
// if (!cfg.learning.nogood.isRstType() && nNogoods < nogoods.length && solver.depth() >= 2) {
// int[] decs = cfg.learning.nogood == ELearningNogood.MIN_STD
// ? solver.rs.getAuxiliarySolver().minimalNogoodExtractor.extractMinimalNogoodFrom(solver, dr.decisions)
// : copy(dr.decisions, -1);
// if (decs != null && decs.length > 3)
// addNogoodFrom(decs);
// assert controlWatches();
// }
// }
// public boolean isBinaryNogoodPresent(int[] decs) {
// assert decs.length == 2;
// WatchCell firstCell = decs[0] > 0 ? positiveWatchLists[dr.numIn(decs[0])][dr.idxIn(decs[0])] :
// negativeWatchLists[dr.numIn(decs[0])][dr.idxIn(decs[0])];
// for (WatchCell cell = firstCell; cell != null; cell = cell.nextCell) {
// int[] cellDecisions = cell.nogood.decisions;
// if (cellDecisions.length == 2
// && ((decs[0] == cellDecisions[0] && decs[1] == cellDecisions[1]) || (decs[0] == cellDecisions[1] && decs[1] ==
// cellDecisions[0])))
// return true;
// }
// return false;
// }
// public void addAllNogoodsOfCurrentBranch() { // en test methode de Julien -
// virer les nogoods triviaux style X != 0 ou X != 8
// Kit.prn(decisionManager);
// display();
// if (tmp == null)
// tmp = new int[solver.problem.variables.length];
//
// int[] decisions = decisionManager.getDecisions();
// int nbMetPositiveDecisions = 0;
// for (int i = 0; i < decisionManager.getNbDecisions(); i++)
// if (decisions[i] > 0)
// tmp[nbMetPositiveDecisions++] = decisions[i];
//
// Kit.prn("nbMet = " + nbMetPositiveDecisions + " nbPast = " +
// solver.getVariableManager().getNbPastVariables());
//
// for (Variable var : solver.variables) {
// Elements elements = var.domain.getElements();
// for (int index = elements.getLastAbsent(); index != -1; index =
// elements.getPrevAbsent(index)) {
// int level = elements.getAbsentLevelOf(index);
// if (level == 0)
// break;
// int[] t = new int[level + 1];
// for (int i = 0; i < t.length - 1; i++)
// t[i] = -tmp[i];
// t[t.length - 1] = decisionManager.getNegativeDecisionFor(variable, index);
// addNogoodFrom(t);
// }
// }
// // Kit.prn(decisionManager);
// // display();
// }
