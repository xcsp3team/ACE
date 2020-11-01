/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;

import constraints.hard.CtrExtension.CtrExtensionGlobal;
import constraints.hard.extension.structures.ExtensionStructure;
import constraints.hard.extension.structures.Table;
import interfaces.TagPositive;
import problem.Problem;
import utility.Kit;
import utility.sets.SetDenseReversible;
import variables.Variable;
import variables.domains.Domain;

public class CtrExtensionGAC4 extends CtrExtensionGlobal implements TagPositive {

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		lastRemoved = Kit.repeat(-1, scp.length);
		int[][] tuples = ((Table) extStructure).tuples;
		assert tuples.length > 0;
		List<Integer>[][] tmp = IntStream.range(0, scp.length)
				.mapToObj(i -> IntStream.range(0, scp[i].dom.initSize()).mapToObj(j -> new ArrayList<Integer>()).toArray(List[]::new)).toArray(List[][]::new);

		ptrs = new int[tuples.length][scp.length];
		for (int i = 0; i < tuples.length; i++)
			for (int j = 0; j < tuples[i].length; j++) {
				int a = tuples[i][j];
				tmp[j][a].add(i);
				ptrs[i][j] = tmp[j][a].size() - 1;
			}
		sups = new SetDenseReversible[scp.length][];
		for (int i = 0; i < sups.length; i++) {
			sups[i] = new SetDenseReversible[scp[i].dom.initSize()];
			for (int j = 0; j < sups[i].length; j++)
				sups[i][j] = new SetDenseReversible(Kit.intArray(tmp[i][j]), true, pb.variables.length + 1);
			// sups[i][j] = tmp[i][j].size() == 0 ? null : new DenseSetMultiLevel(Kit.toIntArray(tmp[i][j]), true, pb.variables.length + 1);
		}
		assert controlStructures();
		for (int i = 0; i < scp.length; i++) {
			Domain dom = scp[i].dom;
			SetDenseReversible[] set = sups[i];
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
							// corresponds to the
							// position of the tuple in the subtable for the value at that position in the tuple

	protected SetDenseReversible[][] sups; // 1d = vap ; 2D = idx

	private int[] lastRemoved; // 1D = variable position ; value = last index (of value) removed

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new Table(this);
	}

	public CtrExtensionGAC4(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(pb.rs.cp.settingSolving.enablePrepro);
	}

	private boolean handleVariableAt(int vap) {
		Domain dom = scp[vap].dom;
		int level = pb.solver.depth();
		int[][] tuples = ((Table) extStructure).tuples;
		for (int a = dom.lastRemoved(); a != lastRemoved[vap]; a = dom.prevRemoved(a)) {
			// Kit.prn(this + " " + dropped + " from " + scope[pos] + " " + lastRemoved[pos]);
			SetDenseReversible droppedSet = sups[vap][a];
			for (int j = droppedSet.limit; j >= 0; j--) {
				int droppedTuplePosition = droppedSet.dense[j];
				int[] tuple = tuples[droppedTuplePosition];
				assert !isValid(tuple);
				for (int k = 0; k < scp.length; k++) {
					Domain domK = scp[k].dom;
					if (domK.isPresent(tuple[k])) {
						SetDenseReversible set = sups[k][tuple[k]];
						int ptr = ptrs[droppedTuplePosition][k];
						if (ptr > set.limit)
							continue; // because already removed
						if (ptr < set.limit) {
							int last = set.last();
							assert ptrs[last][k] == set.limit && set.dense[ptr] == droppedTuplePosition;
							set.removeAtPosition(ptr, level);
							ptrs[droppedTuplePosition][k] = set.limit + 1;
							ptrs[last][k] = ptr;
							assert set.dense[set.limit + 1] == droppedTuplePosition && set.dense[ptr] == last;
						} else
							set.moveLimitAtLevel(1, level);
						if (set.size() == 0 && !domK.remove(tuple[k])) {
							return false;
							// Kit.prn("removal : " + this + " " + scope[k] + " != " + tuple[k] + " (" + k + ")");
						}
					}
				}
			}
			// droppedSet.clearLimitAtLevel(level);
			droppedSet.storeLimitAtLevel(level);
			droppedSet.clear();
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable x) {
		Variable lastPast = pb.solver.futVars.lastPast();
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
		Table table = (Table) extStructure;
		int[][] tuples = table.tuples;
		for (int i = 0; i < ptrs.length; i++) {
			int[] tuple = tuples[i];
			for (int vap = 0; vap < tuple.length; vap++) {
				int ptr = ptrs[i][vap];
				if (sups[vap][tuple[vap]].dense[ptr] != i)
					return false;
			}
		}
		return true;
	}
}

/*
 * for (int i = 0; i < scope.length; i++) { // Kit.prn( " from " + scope[i] + " " + lastRemoved[i]); for (int dropped =
 * domainElements[i].getLastDropped(); dropped != lastRemoved[i]; dropped = domainElements[i].getPrevDropped(dropped)) { // Kit.prn(dropped + " from "
 * + scope[i] + " " + lastRemoved[i]); DenseSetMultiLevel droppedSet = sups[i][dropped]; for (int j = droppedSet.getCurrentLimit(); j >= 0; j--) { int
 * droppedTuplePosition = droppedSet.getDense()[j]; int[] tuple = tuples[droppedTuplePosition]; assert !checkValidityOf(tuple); for (int k = 0; k <
 * scope.length; k++) if (domainElements[k].isPresent(tuple[k])) { DenseSetMultiLevel set = sups[k][tuple[k]]; int position =
 * ptrs[droppedTuplePosition][k]; if (position > set.getCurrentLimit()) continue; // because already removed if (position < set.getCurrentLimit()) {
 * int last = set.getLast(); assert ptrs[last][k] == set.getCurrentLimit() && set.getDense()[position] == droppedTuplePosition;
 * set.removePresentIndexAtPositionAndLevel(position, level); ptrs[droppedTuplePosition][k] = set.getCurrentLimit() + 1; ptrs[last][k] = position;
 * assert set.getDense()[set.getCurrentLimit() + 1] == droppedTuplePosition && set.getDense()[position] == last; } else
 * set.decreaseCurrentLimitFrom(1, level); if (set.getSize() == 0) { if (!propagation.handleReduction( scope[k], domainElements[k].getCurrentSize() -
 * 1)) return false; scope[k].domain.removeElement(tuple[k], this); // Kit.prn("  removal of " + scope[k] + " " + tuple[k]); } } }
 * droppedSet.clear(level); } } for (int i = 0; i < scope.length; i++) lastRemoved[i] = scope[i].domain.getElements().getLastDropped();
 */