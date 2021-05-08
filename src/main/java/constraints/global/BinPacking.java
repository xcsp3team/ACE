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
import interfaces.Tags.TagNotAC;
import problem.Problem;
import sets.SetDense;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

// BinPacking2.py and NursingWorkload and TestBinpacking (dans special)

public final class BinPacking extends CtrGlobal implements ObserverConstruction, ObserverBacktrackingSystematic, TagNotAC { // not call
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
		this.usableBins = new SetSparseReversible(bins.length, true, problem.variables.length + 1);
	}

	@Override
	public void restoreBefore(int depth) {
		usableBins.restoreLimitAtLevel(depth);
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

	private SetDense[] fronts; // fronts[i] is the set of items which are in front of the ith bin (in the ordered sequence of bins) such that i is the first
								// position where they can be put

	private SetSparseReversible usableBins; // set of currently usable bins

	private final long[] sums; // only used when checking values

	public BinPacking(Problem pb, Variable[] scp, int[] sizes, int[] limits) {
		super(pb, scp);
		control(sizes[0] > 0 && Kit.isIncreasing(sizes));
		// defineKey(Kit.join(sizes) + " " + limit);
		control(scp.length >= 2 && Variable.haveSameDomainType(scp)); // TODO to be relaxed when possible

		this.sizes = sizes;
		this.limits = limits;

		int nBins = scp[0].dom.initSize();
		this.bins = IntStream.range(0, nBins).mapToObj(i -> new Bin()).toArray(Bin[]::new);
		this.sortedBins = bins.clone();
		this.fronts = IntStream.range(0, nBins).mapToObj(i -> new SetDense(scp.length)).toArray(SetDense[]::new);

		this.sums = new long[nBins];
	}

	public BinPacking(Problem pb, Variable[] scp, int[] sizes, int limit) {
		this(pb, scp, sizes, Kit.repeat(limit, scp[0].dom.initSize()));
	}

	@Override
	public boolean runPropagator(Variable x) {
		// System.out.println(this);
		// initialization
		for (int j = 0; j <= usableBins.limit; j++) {
			int i = usableBins.dense[j];
			bins[i].set(i, limits[i]); // the bin is reinitialized with its initial capacity
			sortedBins[j] = bins[i];
		}
		// updating the capacity of bins
		for (int i = 0; i < scp.length; i++)
			if (scp[i].dom.size() == 1) {
				bins[scp[i].dom.unique()].capacity -= sizes[i]; // the capacity is updated
				// if (bins[scp[i].dom.unique()].capacity < 0) // TODO why it does not work ?
				// return x.dom.fail();
			}

		// putting each object in front of the right bin (the first one where it can enter)
		int sortLimit = usableBins.limit + 1;
		start: while (true) {
			Arrays.sort(sortedBins, 0, sortLimit, (b1, b2) -> Integer.compare(b1.capacity, b2.capacity)); // increasing sort
			if (sortedBins[0].capacity < 0)
				return x.dom.fail(); // TODO 1: moving it at line 112 (avoid the first sort) ?
			for (SetDense set : fronts) // TODO 2: only clearing from 0 to usableBins.limit ?
				set.clear();
			// for (int ii = futvars.limit; ii >= 0; ii--) {
			// int p = futvars.dense[ii];
			for (int p = 0; p < scp.length; p++) { // TODO 3: only iterating over future variables? (but the condition remains)
				Domain dom = scp[p].dom;
				if (dom.size() == 1)
					continue; // because already considered (when reducing the appropriate bin capacity)
				int position = -1;
				for (int j = 0; position == -1 && j <= usableBins.limit; j++) {
					int i = sortedBins[j].index;
					if (sizes[p] > sortedBins[j].capacity) {
						if (dom.removeValueIfPresent(i) == false)
							return false;
					} else if (dom.present(i)) {
						position = j;
						fronts[j].add(p);
					}
				}
				if (position == -1) {
					return x.dom.fail();
				}
				if (dom.size() == 1) {
					bins[dom.unique()].capacity -= sizes[p]; // note that sortedBins has references to bins
					if (bins[dom.unique()].capacity < 0)
						return x.dom.fail();
					sortLimit = position + 1; // TODO only inserting rather than sorting ?
					continue start;
				}
			}
			break;
		}

		// assert Stream.of(sortedBins).allMatch(bin -> bin.capacity >= 0);

		// energetic reasoning
		int cumulatedCapacities = 0, cumulatedSizes = 0;
		for (int j = usableBins.limit; j >= 0; j--) {
			int capacity = sortedBins[j].capacity;
			cumulatedCapacities += capacity;
			if (fronts[j].size() == 0)
				continue;
			int min = Integer.MAX_VALUE, max = -1;
			for (int k = 0; k <= fronts[j].limit; k++) {
				int size = sizes[fronts[j].dense[k]];
				min = Math.min(min, size);
				max = Math.max(max, size);
				cumulatedSizes += size;
			}
			boolean onyOnePossibleInTheBin = min > capacity / 2;
			int lost = onyOnePossibleInTheBin ? capacity - max : 0; // lost place
			// int l = lost;
			// if (lost > 0)
			// for (int k = j - 1; k >= 0; k--)
			// if (capacity == sortedBins[k].capacity) {
			// if (fronts[k].size() > 0) {
			// System.out.println("gggg");
			// for (int pp = 0; pp <= usableBins.limit; pp++) {
			// System.out.println(sortedBins[pp]);
			// System.out.println(fronts[pp]);
			// }
			//
			// }
			//
			// control(fronts[k].size() == 0);
			// lost += l;
			// } else
			// break;
			// if (lost != l)
			// System.out.println("jjjjj " + lost + " " + l);

			int margin = cumulatedCapacities - lost - cumulatedSizes; // the margin is computed from the object of max size (when only one possible)
			if (margin < 0) {
				return x.dom.fail();
			}
			if (onyOnePossibleInTheBin && margin - (max - min) < 0) { // we can remove some values if the smallest item cannot be put in the bin j
				for (int k = 0; k <= fronts[j].limit; k++) {
					int i = fronts[j].dense[k];
					if (margin - (max - sizes[i]) < 0 && scp[i].dom.removeValueIfPresent(sortedBins[j].index) == false)
						return false;
				}
			}
		}

		boolean b = false;
		if (b)
			return true;
		// we look for the index of the smallest free item
		int smallestFreeItem = -1, minUsableBin = Integer.MAX_VALUE, maxUsableBin = -1;
		for (int i = 0; i < scp.length; i++) {
			if (scp[i].dom.size() > 1) {
				if (smallestFreeItem == -1)
					smallestFreeItem = i;
				minUsableBin = Math.min(minUsableBin, scp[i].dom.first());
				maxUsableBin = Math.max(maxUsableBin, scp[i].dom.last());
			}
		}

		if (smallestFreeItem == -1)
			return true;
		// System.out.println(maxUsableBin);
		// we discard bins that are now identified as useless because we cannot even put the smallest item in it
		for (int j = usableBins.limit; j >= 0; j--) { // for being able to break, we should go from 0 to ..., but removing an element in usableBins could be a
														// pb
			int i = sortedBins[j].index;
			// if (i > maxUsableBin)
			// System.out.println("i= " + i + " max= " + maxUsableBin);
			assert usableBins.isPresent(i);
			if (sortedBins[j].capacity < sizes[smallestFreeItem] || i > maxUsableBin || i < minUsableBin)
				usableBins.remove(i, problem.solver.depth());

		}
		return true;
	}

}
