/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.Arrays;
import java.util.stream.IntStream;

import constraints.Constraint.CtrGlobal;
import interfaces.Observers.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.Observers.ObserverConstruction;
import interfaces.Tags.TagGACUnguaranteed;
import problem.Problem;
import sets.SetDense;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class BinPacking extends CtrGlobal implements ObserverConstruction, ObserverBacktrackingSystematic, TagGACUnguaranteed { // not call
																																		// filtering-complete
	@Override
	public final boolean checkValues(int[] t) {
		Arrays.fill(sums, 0);
		for (int i = 0; i < t.length; i++)
			sums[scp[i].dom.toIdx(t[i])] += sizes[i];
		for (int i = 0; i < sums.length; i++)
			if (sums[i] > limits[i])
				return false;
		return true;
	}

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.setb = new SetSparseReversible(bins.length, true, problem.variables.length + 1);
	}

	@Override
	public void restoreBefore(int depth) {
		setb.restoreLimitAtLevel(depth);
	}

	private static class Bin {
		int index;
		int capacity; // the capacity is updated when possible (when an object is guaranteed to be in it)

		void set(int i, int c) {
			this.index = i;
			this.capacity = c;
		}

		@Override
		public String toString() {
			return "(" + index + ":cap=" + capacity + ")";
		}
	}

	private final int[] sizes;
	private final int[] limits;

	private Bin[] bins;
	private Bin[] sortedBins;

	private SetDense[] positions; // positions[i] is the set of items such that i is the first position (in the ordered sequence of bins) where they can be put

	private final long[] sums; // used for checking values

	private SetSparseReversible setb;

	public BinPacking(Problem pb, Variable[] scp, int[] sizes, int[] limits) {
		super(pb, scp);
		control(Kit.isIncreasing(sizes));
		// defineKey(Kit.join(sizes) + " " + limit);
		control(scp.length >= 2 && Variable.haveSameDomainType(scp)); // TODO checking that all domains are from 0 to nBins-1

		this.sizes = sizes;
		this.limits = limits;

		int nBins = scp[0].dom.initSize();
		this.bins = IntStream.range(0, nBins).mapToObj(i -> new Bin()).toArray(Bin[]::new);
		this.sortedBins = bins.clone();
		this.positions = IntStream.range(0, nBins).mapToObj(i -> new SetDense(scp.length)).toArray(SetDense[]::new);

		this.sums = new long[nBins];
	}

	public BinPacking(Problem pb, Variable[] scp, int[] sizes, int limit) {
		this(pb, scp, sizes, Kit.repeat(limit, scp[0].dom.initSize()));
	}

	@Override
	public boolean runPropagator(Variable x) {
		// System.out.println(this);
		// initialization
		for (int j = 0; j <= setb.limit; j++) {
			int i = setb.dense[j];
			bins[i].set(i, limits[i]);
			sortedBins[j] = bins[i];
		}
		// updating the capacity of bins
		for (int i = 0; i < scp.length; i++)
			if (scp[i].dom.size() == 1)
				bins[scp[i].dom.uniqueValue()].capacity -= sizes[i];

		// putting each object in front of the right bin (the first one where it can enter)
		start: while (true) {
			Arrays.sort(sortedBins, 0, setb.limit + 1, (b1, b2) -> Integer.compare(b1.capacity, b2.capacity));
			if (sortedBins[0].capacity < 0)
				return x.dom.fail();
			for (SetDense set : positions)
				set.clear();
			for (int p = 0; p < scp.length; p++) {
				Domain dom = scp[p].dom;
				if (dom.size() == 1)
					continue; // because already considered (when reducing the appropriate bin capacity)
				boolean foundPosition = false;
				for (int j = 0; !foundPosition && j <= setb.limit; j++) {
					int i = sortedBins[j].index;
					if (sizes[p] > sortedBins[j].capacity) {
						if (dom.removeValueIfPresent(i) == false)
							return false;
					} else if (dom.present(i)) {
						foundPosition = true;
						positions[j].add(p);
					}
				}
				if (!foundPosition) {
					System.out.println("jjjj");
					return x.dom.fail();
				}
				if (dom.size() == 1) {
					bins[dom.uniqueValue()].capacity -= sizes[p];
					continue start;
				}
			}
			break;
		}

		// System.out.println("jjjj1");
		// for (Bin bin : sortedBins)
		// System.out.println(bin);
		// for (SetDense set : positions)
		// System.out.println(set);

		// for (Bin bin : bins)
		// if (bin.capacity < 0)
		// return x.dom.fail();

		// assert Stream.of(sortedBins).allMatch(bin -> bin.capacity >= 0);

		// energetic reasoning
		int cumulatedAvailableCapacities = 0, cumulatedSizes = 0;
		for (int j = setb.limit; j >= 0; j--) {
			int capacity = sortedBins[j].capacity;
			cumulatedAvailableCapacities += capacity;
			if (positions[j].size() == 0)
				continue;
			int min = Integer.MAX_VALUE, max = -1;
			for (int k = 0; k <= positions[j].limit; k++) {
				int size = sizes[positions[j].dense[k]];
				min = Math.min(min, size);
				max = Math.max(max, size);
				cumulatedSizes += size;
			}
			boolean onyOnePossibleInTheBin = min > capacity / 2;
			int lost = onyOnePossibleInTheBin ? capacity - max : 0; // lost place
			int margin = cumulatedAvailableCapacities - lost - cumulatedSizes; // the margin is computed from the object of max size (when only one possible)
			if (margin < 0) {
				return x.dom.fail();
			}
			if (onyOnePossibleInTheBin && margin - (max - min) < 0) { // we can remove some values if the smallest item cannot be put in the bin j
				for (int k = 0; k <= positions[j].limit; k++) {
					int i = positions[j].dense[k];
					if (margin - (max - sizes[i]) < 0 && scp[i].dom.removeValueIfPresent(sortedBins[j].index) == false)
						return false;
				}
			}
		}

		boolean b = true;
		if (b)
			return true;
		int smallest = -1;
		for (int i = 0; smallest == -1 && i < scp.length; i++)
			if (scp[i].dom.size() > 1)
				smallest = i;
		if (smallest == -1)
			return true;
		// System.out.println("at " + problem.solver.depth() + " samllest " + bins.length + " " + sizes[smallest] + " " + setb.size());
		int pos = -1;
		for (int j = setb.limit; j >= 0; j--) {
			if (!setb.isPresent(sortedBins[j].index))
				System.exit(1);

			if (sortedBins[j].capacity < smallest)
				setb.remove(sortedBins[j].index, problem.solver.depth());
		}

		return true;
	}

}
