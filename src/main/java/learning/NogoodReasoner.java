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

import static java.util.stream.Collectors.joining;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import dashboard.Control.OptionsLearning;
import sets.SetDense;
import solver.Decisions;
import solver.Solver;
import utility.Kit;
import variables.Variable;

/**
 * This class allows us to record and reason with nogoods.
 * 
 * @author Christophe Lecoutre
 */
public final class NogoodReasoner {

	/**
	 * Builds and returns an object used for recording and reasoning with nogoods, or null
	 * 
	 * @param solver
	 *            the solver to which the built reasoner will be attached
	 * @return an object recording and reasoning with nogoods, or null
	 */
	public static NogoodReasoner buildFor(Solver solver) {
		if (solver.head.control.solving.enableSearch && solver.head.control.learning.nogood != LearningNogood.NO && solver.propagation.queue != null)
			return new NogoodReasoner(solver);
		return null;
	}

	/**
	 * Different ways of learning nogoods.
	 */
	public static enum LearningNogood {
		NO, RST, RST_MIN, RST_SYM;

		/**
		 * @return true is the learning mechanism is related to restarts
		 */
		public boolean isRstType() {
			return this == RST || this == RST_MIN || this == RST_SYM;
		}
	}

	/**********************************************************************************************
	 * Fields and constructor
	 *********************************************************************************************/

	/**
	 * Class for cells used in linked lists.
	 */
	private static final class WatchCell {

		/**
		 * The nogood recorded in the cell
		 */
		private Nogood nogood;

		/**
		 * The next cell, following this one, or null
		 */
		private WatchCell next;

		private WatchCell(Nogood nogood, WatchCell next) {
			this.nogood = nogood;
			this.next = next;
		}
	}

	/**
	 * The solver to which this object is attached
	 */
	public final Solver solver;

	/**
	 * The decisions taken by the solver (redundant field)
	 */
	public final Decisions decisions;

	/**
	 * The options concerning learning
	 */
	final OptionsLearning options;

	/**
	 * Arrays with recorded nogoods (at indexes ranging from 0 to nNogoods, excluded)
	 */
	private Nogood[] nogoods;

	/**
	 * The number of recorded nogoods
	 */
	public int nNogoods;

	/**
	 * Positive watch lists; pws[x][a] is the first cell (nogood) involving the positive literal (x=a) as being watched
	 */
	private final WatchCell[][] pws;

	/**
	 * Negative watch lists; nws[x][a] is the first cell (nogood) involving the negative literal (x!=a) as being watched
	 */
	private final WatchCell[][] nws;

	/**
	 * The first free cell (i.e. from the pool of free cells)
	 */
	private WatchCell free;

	/**
	 * A temporary array
	 */
	private int[] tmp;

	// NogoodMinimizer nogoodMinimizer;
	// SymmetryHandler symmetryHandler;

	/**
	 * Builds an object recording and reasoning with nogoods for the specified solver
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public NogoodReasoner(Solver solver) {
		this.solver = solver;
		this.decisions = solver.decisions;
		this.options = solver.head.control.learning;
		this.nogoods = new Nogood[options.nogoodBaseLimit];
		this.pws = Stream.of(solver.problem.variables).map(x -> new WatchCell[x.dom.initSize()]).toArray(WatchCell[][]::new);
		this.nws = Stream.of(solver.problem.variables).map(x -> new WatchCell[x.dom.initSize()]).toArray(WatchCell[][]::new);
		this.tmp = new int[solver.problem.variables.length];
		// nogoodMinimizer = options.nogood == LearningNogood.RST_MIN ? new NogoodMinimizer(solver) : null;
		// symmetryHandler = options.nogood == RST_SYM ? new SymmetryHandler(this,problem.variables.length) : null;
	}

	/**
	 * Clears the nogood base
	 */
	public void reset() {
		nNogoods = 0;
		for (WatchCell[] t : pws) // TODO put them in free instead
			Arrays.fill(t, null);
		for (WatchCell[] t : nws) // TODO put them in free instead
			Arrays.fill(t, null);
		// control(symmetryHandler == null);
	}

	/**
	 * Important: currently not caleld
	 * 
	 * @param t
	 *            a tuple of indexes (of values)
	 * @return true if the tuple of values corresponding to the specified tuple of indexes satisfies the nogoods
	 */
	public boolean checkIndexes(int[] t) {
		// note that nogoods are stored with indexes of values
		extern: for (int i = 0; i < nNogoods; i++) {
			for (int d : nogoods[i].decisions) {
				int x = decisions.numIn(d);
				int a = decisions.idxIn(d);
				if (t[x] != a)
					continue extern;
			}
			return false;
		}
		return true;
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
		int[] literals = nogood.decisions;
		int start = nogood.getWatch(firstWatch);
		int r = literals.length, limit = r + start;
		for (int j = start + 1; j < limit; j++) {
			int i = j % r; // going from start+1 to literals.length and from 0 to start
			if (!nogood.isWatch(i) && canBeWatched(literals[i])) {
				addWatchFor(nogood, i, firstWatch);
				return true;
			}
		}
		return false;
	}

	/**
	 * Applies the specified decision
	 * 
	 * @param decision
	 *            the decision to be applied
	 * @return false if an inconsistency is detected
	 */
	private boolean apply(int decision) {
		Variable x = decisions.varIn(decision);
		int a = decisions.idxIn(decision);
		solver.propagation.currFilteringCtr = null;
		return decision > 0 ? x.dom.reduceTo(a) : x.dom.removeIfPresent(a);
	}

	private boolean checkWatchesOf(WatchCell[] watchCells, int a, int watchedDecision) {
		WatchCell previous = null, current = watchCells[a];
		while (current != null) {
			Nogood nogood = current.nogood;
			int watchedDecision2 = nogood.watchedDecisionOtherThan(watchedDecision);
			if (!decisions.varIn(watchedDecision2).dom.contains(decisions.idxIn(watchedDecision2))) {
				previous = current;
				current = current.next;
			} else if (canFindAnotherWatchFor(nogood, nogood.firstWatchedDecision() == watchedDecision)) {
				WatchCell tmp = current.next;
				if (previous == null)
					watchCells[a] = current.next;
				else
					previous.next = current.next;
				current.next = free;
				free = current;
				current = tmp;
			} else {
				previous = current;
				current = current.next;
				if (apply(nogood.watchedDecisionOtherThan(watchedDecision)) == false)
					return false;
			}
		}
		assert controlWatches();
		return true;
	}

	/**
	 * Checks and infers the consequences of the specified decision
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            a value index for x
	 * @param positive
	 *            true if the studied decision is positive (x=a), false if it is negative (x != a)
	 * @return false if an inconsistency is detected
	 */
	public boolean checkWatchesOf(Variable x, int a, boolean positive) {
		return positive ? checkWatchesOf(pws[x.num], a, decisions.positiveDecisionFor(x.num, a))
				: checkWatchesOf(nws[x.num], a, decisions.negativeDecisionFor(x.num, a));
	}

	// public boolean runPropagator(Variable x) {
	// return x.dom.size() > 1 || checkWatchesOf(x, x.dom.first(), false);
	// }

	/**********************************************************************************************
	 * About recording
	 *********************************************************************************************/

	private void addWatchFor(Nogood nogood, int position, boolean firstWatch) {
		int decision = nogood.decisions[position];
		WatchCell[] cells = decision > 0 ? pws[decisions.numIn(decision)] : nws[decisions.numIn(decision)];
		int a = decisions.idxIn(decision);
		if (free == null)
			cells[a] = new WatchCell(nogood, cells[a]);
		else {
			WatchCell cell = free;
			free = free.next;
			cell.nogood = nogood;
			cell.next = cells[a];
			cells[a] = cell;
		}
		nogood.setWatch(position, firstWatch);
	}

	/**
	 * Adds a nogood from the specified (negative) decisions
	 * 
	 * @param negativeDecisions
	 *            the (negative) decisions forming the nogood to be added
	 * @param toBeSorted
	 *            true if the decisions must be sorted
	 */
	public void addNogood(int[] negativeDecisions, boolean toBeSorted) {
		// if (negativeDecisions.length < 3) {
		// System.out.println(" nog : " + IntStream.of(negativeDecisions).mapToObj(d ->
		// decisions.stringOf(d)).collect(joining(" ")));
		// }

		if (nNogoods < nogoods.length) {
			if (toBeSorted)
				Arrays.sort(negativeDecisions);
			Nogood nogood = new Nogood(negativeDecisions);
			nogoods[nNogoods++] = nogood;
			addWatchFor(nogood, negativeDecisions.length - 2, true);
			addWatchFor(nogood, negativeDecisions.length - 1, false);
			// if (symmetryHandler != null) symmetryHandler.addNogood(decs);
		}
	}

	/**
	 * Adds all nogoods that can be extracted from the current branch
	 */
	public void addNogoodsOfCurrentBranch() {
		SetDense set = decisions.set;
		if (!options.nogood.isRstType() || set.size() < 2)
			return;
		int nMetPositiveDecisions = 0;
		for (int i = 0; i <= set.limit; i++) {
			int d = set.dense[i];
			if (d > 0)
				tmp[nMetPositiveDecisions++] = d;
			else if (nMetPositiveDecisions > 0) {
				int[] negativeDecisions = new int[nMetPositiveDecisions + 1];
				// if (options.nogood == LearningNogood.RST_MIN && decisions.isFailedAssignment(i)) {
				// boolean bottomUp = true; // hard coding
				// for (int j = 0; j < nMetPositiveDecisions; j++)
				// currentNogood[j] = tmp[bottomUp ? nMetPositiveDecisions - j - 1 : j];
				// currentNogood[currentNogood.length - 1] = -d;
				// int[] minimizedNogood = nogoodMinimizer.extractMinimalNogoodFrom(currentNogood);
				// if (minimizedNogood != null) {
				// if (minimizedNogood.length == 0)
				// return; // inconsistency proved
				// addNogood(minimizedNogood, false); // symmetryHandler != null);
				// }
				// } else {
				// record negative decisions for direct insertion of the nogod
				for (int j = 0; j < nMetPositiveDecisions; j++)
					negativeDecisions[j] = -tmp[j];
				negativeDecisions[nMetPositiveDecisions] = d;
				addNogood(negativeDecisions, false); // symmetryHandler != null);
				// }
				// if (symmetryHandler != null) symmetryHandler.handleSymmetricNaryNogoods(currentNogood);
			}
			// else if (symmetryHandler != null) symmetryHandler.handleSymmetricUnaryNogoods(d);
		}
		// if (nNogoods > 800) {
		// System.out.println(this);
		// System.exit(1);
		// }
		assert controlWatches();
	}

	private boolean controlLists(WatchCell[][] watches, boolean positive) {
		for (int x = 0; x < watches.length; x++)
			for (int a = 0; a < watches[x].length; a++) {
				int decision = positive ? decisions.positiveDecisionFor(x, a) : decisions.negativeDecisionFor(x, a);
				for (WatchCell cell = watches[x][a]; cell != null; cell = cell.next)
					if (!cell.nogood.isDecisionWatched(decision)) {
						Kit.log.warning("nogood = " + cell.nogood + " is not watched");
						return false;
					}
			}
		return true;
	}

	private boolean controlNogood(int watchedDecision, Nogood nogood) {
		int x = decisions.numIn(watchedDecision), a = decisions.idxIn(watchedDecision);
		WatchCell first = watchedDecision > 0 ? pws[x][a] : nws[x][a];
		for (WatchCell cell = first; cell != null; cell = cell.next)
			if (cell.nogood == nogood)
				return true;
		return false;
	}

	private boolean controlWatches() {
		if (!controlLists(pws, true) || !controlLists(nws, false))
			return false;
		for (int i = 0; i < nNogoods; i++) {
			if (nogoods[i] == null)
				continue;
			if (!controlNogood(nogoods[i].firstWatchedDecision(), nogoods[i]) || !controlNogood(nogoods[i].secondWatchedDecision(), nogoods[i]))
				return false;
		}
		return true;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder("Nogoods = {\n");
		for (int i = 0; i < nNogoods; i++)
			sb.append(IntStream.of(nogoods[i].decisions).mapToObj(d -> decisions.stringOf(d)).collect(joining(" "))).append("\n");
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
