/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package learning;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import dashboard.Control.SettingLearning;
import interfaces.Observers.ObserverRuns;
import solver.backtrack.DecisionRecorder;
import solver.backtrack.SolverBacktrack;
import utility.Enums.ELearningNogood;
import utility.Enums.EStopping;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class NogoodRecorder {

	public static NogoodRecorder buildFor(SolverBacktrack solver) {
		if (solver.head.control.solving.enableSearch && solver.head.control.learning.nogood != ELearningNogood.NO
				&& solver.propagation.queue != null)
			return new NogoodRecorder(solver);
		return null;
	}

	public boolean checkValues(int[] t) {
		extern: for (int i = 0; i < nNogoods; i++) {
			for (int d : nogoods[i].decisions) {
				int x = dr.numIn(d);
				int a = dr.idxIn(d);
				if (t[x] != a)
					continue extern;
			}
			return false;
		}
		return true;
	}

	public boolean checkIndexes(int[] t) {
		return checkValues(t); // because nogoods are stored with indexes of values
	}

	private boolean dealWithInference(int inferenceDecision) {
		Variable x = dr.varIn(inferenceDecision);
		int a = dr.idxIn(inferenceDecision);
		solver.propagation.currFilteringCtr = null;
		Domain dom = x.dom;
		if (inferenceDecision > 0)
			return dom.reduceTo(a);
		else
			return dom.removeIfPresent(a);

		// if (inferenceDecision > 0) {
		// if (!dom.isPresent(a))
		// return false;
		// if (dom.size() == 1)
		// return true;
		// for (int b = dom.first(); b != -1; b = dom.next(b))
		// if (b != a)
		// dom.removeElementary(b);
		// } else {
		// if (!dom.isPresent(a))
		// return true;
		// if (dom.size() == 1)
		// return false;
		// dom.removeElementary(a);
		// }
		// solver.propagation.queue.add(x);
		// return true;
	}

	private boolean checkWatchesOf(WatchCell[] watchCells, int a, int watchedDecision) {
		WatchCell previous = null, current = watchCells[a];
		while (current != null) {
			Nogood nogood = current.nogood;
			int watchedDecision2 = nogood.getSecondWatchedDecision(watchedDecision);
			if (!dr.varIn(watchedDecision2).dom.present(dr.idxIn(watchedDecision2))) {
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
		return positive ? checkWatchesOf(pws[x.num], a, dr.positiveDecisionFor(x.num, a)) : checkWatchesOf(nws[x.num], a, dr.negativeDecisionFor(x.num, a));
	}

	public boolean runPropagator(Variable x) {
		if (x.dom.size() == 1 && checkWatchesOf(x, x.dom.first(), false) == false)
			return false;
		return true;
	}

	private class WatchCell {

		private Nogood nogood;

		private WatchCell nextCell;

		private WatchCell(Nogood nogood, WatchCell nextCell) {
			this.nogood = nogood;
			this.nextCell = nextCell;
		}
	}

	private final SolverBacktrack solver;

	private final DecisionRecorder dr; // redundant field

	private final SettingLearning settings;

	private Nogood[] nogoods;

	public int nNogoods;

	private final WatchCell[][] pws; // positive watch lists; pws[x][a] is the first cell (so, nogood) involving the positive literal (x=a) as being watched

	private final WatchCell[][] nws; // negative watch lists; nws[x][a] is the first cell (nogood) involving the negative literal (x!=a) as being watched

	private WatchCell free; // reference to the first free cell (i.e. the pool of free cells)

	public final SymmetryHandler symmetryHandler;

	private int[] tmp;

	public void reset() {
		nNogoods = 0;
		Kit.fill(pws, null); // TODO put them in free instead
		Kit.fill(nws, null); // TODO put them in free instead
		Kit.control(symmetryHandler == null);
	}

	public NogoodRecorder(SolverBacktrack solver) {
		this.solver = solver;
		this.dr = solver.dr;
		this.settings = solver.head.control.learning;
		this.nogoods = new Nogood[settings.nogoodBaseLimit];
		this.pws = Stream.of(solver.problem.variables).map(x -> new WatchCell[x.dom.initSize()]).toArray(WatchCell[][]::new);
		this.nws = Stream.of(solver.problem.variables).map(x -> new WatchCell[x.dom.initSize()]).toArray(WatchCell[][]::new);
		this.tmp = new int[solver.problem.variables.length];
		this.symmetryHandler = settings.nogood == ELearningNogood.RST_SYM ? new SymmetryHandler(solver.problem.variables.length) : null;
		solver.propagation.queue.nogoodRecorder = this;
	}

	private void addWatchFor(Nogood nogood, int position, boolean firstWatch) {
		int decision = nogood.decisions[position];
		WatchCell[] cells = decision > 0 ? pws[dr.numIn(decision)] : nws[dr.numIn(decision)];
		int a = dr.idxIn(decision);
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

	private boolean canBeWatched(int decision) {
		assert decision != 0;
		Variable x = dr.varIn(decision);
		int a = dr.idxIn(decision);
		return decision > 0 ? x.dom.present(a) : x.dom.size() > 1 || !x.dom.present(a);
	}

	private boolean canFindAnotherWatchFor(Nogood nogood, boolean firstWatch) {
		int[] decs = nogood.decisions;
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

	private void addNogood(int[] decs, boolean toBeSorted) {
		if (nNogoods < nogoods.length) {
			decs = toBeSorted ? Kit.sort(decs) : decs;
			Nogood nogood = nogoods[nNogoods++] = new Nogood(decs);
			addWatchFor(nogood, decs.length - 2, true);
			addWatchFor(nogood, decs.length - 1, false);
			if (symmetryHandler != null)
				symmetryHandler.addNogood(decs);
		}
	}

	public void addNogoodsOfCurrentBranch() {
		if (!settings.nogood.isRstType() || dr.decisions.size() < 2)
			return;
		int nMetPositiveDecisions = 0;
		for (int i = 0; i <= dr.decisions.limit; i++) {
			int d = dr.decisions.dense[i];
			if (d > 0)
				tmp[nMetPositiveDecisions++] = d;
			else if (nMetPositiveDecisions > 0) {
				int[] currentNogood = new int[nMetPositiveDecisions + 1];
				if (settings.nogood == ELearningNogood.RST_MIN && dr.isFailedAssignment(i)) {
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
						addNogood(minimizedNogood, symmetryHandler != null);
					}
				} else { // if (dr.isFailedAssignment(i)){
							// record negative decisions for direct insertion of the nogod
					for (int j = 0; j < nMetPositiveDecisions; j++)
						currentNogood[j] = -tmp[j];
					currentNogood[nMetPositiveDecisions] = d;
					addNogood(currentNogood, symmetryHandler != null);
				}
				if (symmetryHandler != null)
					symmetryHandler.handleSymmetricNaryNogoods(currentNogood);
			} else if (symmetryHandler != null)
				symmetryHandler.handleSymmetricUnaryNogoods(d);
		}
		// display();
		assert controlWatches();
	}

	private boolean control(WatchCell[][] watches, boolean positive) {
		for (int i = 0; i < watches.length; i++)
			for (int j = 0; j < watches[i].length; j++)
				for (WatchCell cell = watches[i][j]; cell != null; cell = cell.nextCell)
					if (!cell.nogood.isDecisionWatched(positive ? dr.positiveDecisionFor(i, j) : dr.negativeDecisionFor(i, j))) {
						Kit.log.warning("nogood = " + cell.nogood + " does not watch");
						return false;
					}
		return true;
	}

	private boolean controlNogood(int wdec, Nogood nogood) {
		WatchCell firstCell = wdec > 0 ? pws[dr.numIn(wdec)][dr.idxIn(wdec)] : nws[dr.numIn(wdec)][dr.idxIn(wdec)];
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

	private class SymmetryHandler implements ObserverRuns {

		@Override
		public void beforeRun() {
			boolean effective = false;
			for (int decision : decisionsToBePerformedAtNextRun) {
				Variable x = dr.varIn(decision);
				int a = dr.idxIn(decision);
				if (x.dom.present(a)) {
					x.dom.removeElementary(a);
					Kit.log.info("Remove Unary sym nogood : " + dr.stringOf(decision));
					if (x.dom.size() == 0) {
						solver.stopping = EStopping.FULL_EXPLORATION;
						break;
					}
					effective = true;
				}
			}
			decisionsToBePerformedAtNextRun.clear();
			if (solver.stopping != EStopping.FULL_EXPLORATION && effective && !solver.propagation.runInitially())
				solver.stopping = EStopping.FULL_EXPLORATION;
		}

		private Map<Integer, Integer>[] mapOfSymmetryGroupGenerators;

		private Set<int[]>[] nogoodsSetsBySize;

		private int[][] tmps; // tmps[i] is a temporary array of size i; built in a lazy manner

		private Set<Integer> decisionsToBePerformedAtNextRun = new HashSet<>();

		private final int unaryLimit, nonunaryLimit;

		private List<Integer> unaryNogoodsToHandle = new ArrayList<>();

		private LinkedList<int[]> naryNogoodsToHandle = new LinkedList<>();

		private SymmetryHandler(int nVariables) {
			this.mapOfSymmetryGroupGenerators = new Map[solver.problem.symmetryGroupGenerators.size()];
			int cnt = 0;
			for (List<int[]> generator : solver.problem.symmetryGroupGenerators) {
				Map<Integer, Integer> map = mapOfSymmetryGroupGenerators[cnt] = new HashMap<>();
				for (int[] cycle : generator)
					for (int i = 0; i < cycle.length; i++)
						map.put(cycle[i], cycle[(i + 1) % cycle.length]);
				cnt++;
			}
			this.nogoodsSetsBySize = new TreeSet[nVariables + 1];
			this.tmps = new int[nVariables + 1][];
			this.unaryLimit = settings.unarySymmetryLimit;
			this.nonunaryLimit = settings.nonunarySymmetryLimit;
		}

		private void addNogood(int[] decs) {
			assert nNogoods < nogoods.length;
			(nogoodsSetsBySize[decs.length] == null ? nogoodsSetsBySize[decs.length] = new TreeSet<>(Utilities.lexComparatorInt)
					: nogoodsSetsBySize[decs.length]).add(decs);
		}

		private void handleSymmetricUnaryNogoods(int decision) {
			unaryNogoodsToHandle.clear();
			unaryNogoodsToHandle.add(decision);
			for (int i = 0; i < unaryLimit && unaryNogoodsToHandle.size() != 0; i++) {
				int pickedDecision = unaryNogoodsToHandle.remove(unaryNogoodsToHandle.size() - 1);
				int a = dr.idxIn(pickedDecision);
				int x = dr.numIn(pickedDecision);
				for (Map<Integer, Integer> map : mapOfSymmetryGroupGenerators) {
					Integer y = map.get(x);
					if (y != null) {
						int symmetricDecision = dr.negativeDecisionFor(y, a);
						if (!decisionsToBePerformedAtNextRun.contains(symmetricDecision)) {
							decisionsToBePerformedAtNextRun.add(symmetricDecision);
							unaryNogoodsToHandle.add(symmetricDecision);
						}
					}
				}
			}
		}

		private void handleSymmetricNaryNogoods(int[] initialNogood) {
			naryNogoodsToHandle.clear();
			naryNogoodsToHandle.add(initialNogood);
			int currentSpace = 0;
			while (currentSpace < nonunaryLimit && naryNogoodsToHandle.size() != 0) {
				int[] pickedNogood = naryNogoodsToHandle.poll(); // removeLast();
				assert Kit.isIncreasing(pickedNogood);
				int[] currentSymmetricNogood = tmps[pickedNogood.length] == null ? tmps[pickedNogood.length] = new int[pickedNogood.length]
						: tmps[pickedNogood.length];
				for (Map<Integer, Integer> map : mapOfSymmetryGroupGenerators) {
					boolean changed = false;
					for (int j = 0; j < pickedNogood.length; j++) {
						int a = dr.idxIn(pickedNogood[j]);
						int x = dr.numIn(pickedNogood[j]);
						Integer y = map.get(x);
						if (y != null) {
							// if (solver.problem.getVariable(symmetricId).domain.getElements().getDroppedLevelFor(index) == 0) {
							// changed = false; break; }
							currentSymmetricNogood[j] = dr.negativeDecisionFor(y, a);
							changed = true;
						} else
							currentSymmetricNogood[j] = dr.negativeDecisionFor(x, a);
					}
					if (changed) {
						Arrays.sort(currentSymmetricNogood);
						if (!nogoodsSetsBySize[currentSymmetricNogood.length].contains(currentSymmetricNogood)) {
							int[] symmetricNogood = currentSymmetricNogood.clone();
							NogoodRecorder.this.addNogood(symmetricNogood, false);
							naryNogoodsToHandle.add(symmetricNogood);
							currentSpace += symmetricNogood.length * symmetricNogood.length;
							// display(symmetricNogood);
						}
					}
				}
			}
		}
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
// && ((decs[0] == cellDecisions[0] && decs[1] == cellDecisions[1]) || (decs[0] == cellDecisions[1] && decs[1] == cellDecisions[0])))
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
