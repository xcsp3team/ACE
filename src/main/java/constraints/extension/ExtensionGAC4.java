/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;

import constraints.extension.Extension.ExtensionGlobal;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import interfaces.Tags.TagPositive;
import problem.Problem;
import sets.SetDenseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public class ExtensionGAC4 extends ExtensionGlobal implements TagPositive {

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();

		int[][] tuples = ((Table) extStructure).tuples;
		assert tuples.length > 0;
		List<Integer>[][] tmp = IntStream.range(0, scp.length)
				.mapToObj(i -> IntStream.range(0, scp[i].dom.initSize()).mapToObj(j -> new ArrayList<Integer>()).toArray(List[]::new)).toArray(List[][]::new);

		this.ptrs = new int[tuples.length][scp.length];
		for (int i = 0; i < tuples.length; i++)
			for (int x = 0; x < tuples[i].length; x++) {
				int a = tuples[i][x];
				tmp[x][a].add(i);
				ptrs[i][x] = tmp[x][a].size() - 1;
			}
		this.sups = new SetDenseReversible[scp.length][];
		for (int x = 0; x < sups.length; x++) {
			sups[x] = new SetDenseReversible[scp[x].dom.initSize()];
			for (int a = 0; a < sups[x].length; a++)
				sups[x][a] = new SetDenseReversible(Kit.intArray(tmp[x][a]), true, problem.variables.length + 1);
		}
		this.lastRemoved = Kit.repeat(-1, scp.length);

		assert controlStructures();
		for (int x = 0; x < scp.length; x++) {
			Domain dom = scp[x].dom;
			SetDenseReversible[] set = sups[x];
			dom.execute(a -> {
				if (set[a].size() == 0)
					dom.removeAtConstructionTime(a);
			});
		}
	}

	@Override
	public void restoreBefore(int depth) {
		for (int i = 0; i < sups.length; i++)
			for (int j = 0; j < sups[i].length; j++)
				if (sups[i][j] != null)
					sups[i][j].restoreLimitAtLevel(depth);
		Arrays.fill(lastRemoved, -1);
	}

	// private Boolean finishedPreprocessing;

	protected int[][] ptrs; // The set of pointers. The first array index corresponds to the order of the tuples. The second array index
							// corresponds to the position of the tuple in the subtable for the value at that position in the tuple

	protected SetDenseReversible[][] sups;

	private int[] lastRemoved;

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new Table(this);
	}

	public ExtensionGAC4(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(pb.head.control.solving.enablePrepro);
	}

	private boolean handleVariableAt(int x) {
		Domain dom = scp[x].dom;
		int depth = problem.solver.depth();
		int[][] tuples = ((Table) extStructure).tuples;
		for (int a = dom.lastRemoved(); a != lastRemoved[x]; a = dom.prevRemoved(a)) {
			SetDenseReversible droppedSet = sups[x][a];
			for (int j = droppedSet.limit; j >= 0; j--) {
				int droppedTuplePosition = droppedSet.dense[j];
				int[] tuple = tuples[droppedTuplePosition];
				assert !isValid(tuple);
				for (int y = 0; y < scp.length; y++) {
					if (scp[y].dom.isPresent(tuple[y])) {
						SetDenseReversible set = sups[y][tuple[y]];
						int ptr = ptrs[droppedTuplePosition][y];
						if (ptr > set.limit)
							continue; // because already removed
						if (ptr < set.limit) {
							int last = set.last();
							assert ptrs[last][y] == set.limit && set.dense[ptr] == droppedTuplePosition;
							set.removeAtPosition(ptr, depth);
							ptrs[droppedTuplePosition][y] = set.limit + 1;
							ptrs[last][y] = ptr;
							assert set.dense[set.limit + 1] == droppedTuplePosition && set.dense[ptr] == last;
						} else
							set.moveLimitAtLevel(1, depth);
						if (set.size() == 0 && !scp[y].dom.remove(tuple[y])) {
							return false;
						}
					}
				}
			}
			// droppedSet.clearLimitAtLevel(level);
			droppedSet.storeLimitAtLevel(depth);
			droppedSet.clear();
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable x) {
		Variable lastPast = problem.solver.futVars.lastPast();
		if (x == lastPast && !handleVariableAt(positionOf(x)))
			return false;
		for (int i = futvars.limit; i >= 0; i--)
			if (!handleVariableAt(futvars.dense[i]))
				return false;
		for (int i = futvars.limit; i >= 0; i--)
			lastRemoved[futvars.dense[i]] = scp[futvars.dense[i]].dom.lastRemoved();
		assert controlStructures();
		return true;
	}

	private boolean controlStructures() {
		int[][] tuples = ((Table) extStructure).tuples;
		for (int i = 0; i < ptrs.length; i++) {
			int[] tuple = tuples[i];
			for (int x = 0; x < tuple.length; x++) {
				int ptr = ptrs[i][x];
				if (sups[x][tuple[x]].dense[ptr] != i)
					return false;
			}
		}
		return true;
	}
}

/*
 * for (int i = 0; i < scope.length; i++) { // Kit.prn( " from " + scope[i] + " " + lastRemoved[i]); for (int dropped = domainElements[i].getLastDropped();
 * dropped != lastRemoved[i]; dropped = domainElements[i].getPrevDropped(dropped)) { // Kit.prn(dropped + " from " + scope[i] + " " + lastRemoved[i]);
 * DenseSetMultiLevel droppedSet = sups[i][dropped]; for (int j = droppedSet.getCurrentLimit(); j >= 0; j--) { int droppedTuplePosition =
 * droppedSet.getDense()[j]; int[] tuple = tuples[droppedTuplePosition]; assert !checkValidityOf(tuple); for (int k = 0; k < scope.length; k++) if
 * (domainElements[k].isPresent(tuple[k])) { DenseSetMultiLevel set = sups[k][tuple[k]]; int position = ptrs[droppedTuplePosition][k]; if (position >
 * set.getCurrentLimit()) continue; // because already removed if (position < set.getCurrentLimit()) { int last = set.getLast(); assert ptrs[last][k] ==
 * set.getCurrentLimit() && set.getDense()[position] == droppedTuplePosition; set.removePresentIndexAtPositionAndLevel(position, level);
 * ptrs[droppedTuplePosition][k] = set.getCurrentLimit() + 1; ptrs[last][k] = position; assert set.getDense()[set.getCurrentLimit() + 1] == droppedTuplePosition
 * && set.getDense()[position] == last; } else set.decreaseCurrentLimitFrom(1, level); if (set.getSize() == 0) { if (!propagation.handleReduction( scope[k],
 * domainElements[k].getCurrentSize() - 1)) return false; scope[k].domain.removeElement(tuple[k], this); // Kit.prn("  removal of " + scope[k] + " " +
 * tuple[k]); } } } droppedSet.clear(level); } } for (int i = 0; i < scope.length; i++) lastRemoved[i] = scope[i].domain.getElements().getLastDropped();
 */