/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension;

import static utility.Kit.control;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;

import constraints.ConstraintExtension.ExtensionSpecific;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import interfaces.Tags.TagPositive;
import problem.Problem;
import sets.SetDenseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class GAC4 extends ExtensionSpecific implements TagPositive {

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new Table(this);
	}

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.tuples = ((Table) extStructure()).tuples;

		List<Integer>[][] tmp = IntStream.range(0, scp.length)
				.mapToObj(i -> IntStream.range(0, scp[i].dom.initSize()).mapToObj(j -> new ArrayList<>()).toArray(List[]::new)).toArray(List[][]::new);

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
				sups[x][a] = new SetDenseReversible(Kit.intArray(tmp[x][a]), problem.variables.length + 1, true);
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

	/**
	 * The tuples of the table (redundant field)
	 */
	private int[][] tuples;

	/**
	 * The set of pointers. The first array index corresponds to the order of the tuples. The second array index corresponds to the position of the tuple in the
	 * subtable for the value at that position in the tuple
	 */
	private int[][] ptrs;

	private SetDenseReversible[][] sups;

	private int[] lastRemoved;

	public GAC4(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(pb.head.control.solving.enablePrepro);
	}

	private boolean handleVariableAt(int x) {
		Domain dom = scp[x].dom;
		int depth = problem.solver.depth();
		for (int a = dom.lastRemoved(); a != lastRemoved[x]; a = dom.prevRemoved(a)) {
			SetDenseReversible droppedSet = sups[x][a];
			for (int j = droppedSet.limit; j >= 0; j--) {
				int droppedTuplePosition = droppedSet.dense[j];
				int[] tuple = tuples[droppedTuplePosition];
				assert !isValid(tuple);
				for (int y = 0; y < scp.length; y++) {
					if (scp[y].dom.contains(tuple[y])) {
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
		for (int i = 0; i < ptrs.length; i++) {
			int[] tuple = tuples[i];
			for (int x = 0; x < tuple.length; x++)
				if (sups[x][tuple[x]].dense[ptrs[i][x]] != i)
					return false;
		}
		return true;
	}
}
