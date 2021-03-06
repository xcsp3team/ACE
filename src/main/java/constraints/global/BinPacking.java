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
import java.util.stream.Stream;

import constraints.Constraint.CtrGlobal;
import interfaces.Tags.TagGACUnguaranteed;
import problem.Problem;
import sets.SetDense;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class BinPacking extends CtrGlobal implements TagGACUnguaranteed { // not call filtering-complete
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

	public BinPacking(Problem pb, Variable[] scp, int[] sizes, int[] limits) {
		super(pb, scp);
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
		for (int i = 0; i < bins.length; i++) {
			bins[i].set(i, limits[i]);
			sortedBins[i] = bins[i];
		}
		// updating the capacity of bins
		for (int i = 0; i < scp.length; i++)
			if (scp[i].dom.size() == 1)
				sortedBins[scp[i].dom.uniqueValue()].capacity -= sizes[i];

		// putting each object in front of the right bin (the first one where it can enter)
		start: while (true) {
			Arrays.sort(sortedBins, (b1, b2) -> Integer.compare(b1.capacity, b2.capacity));
			for (SetDense set : positions)
				set.clear();
			for (int i = 0; i < scp.length; i++) {
				Domain dom = scp[i].dom;
				if (dom.size() == 1)
					continue; // because already considered (when reducing the appropriate bin capacity)
				boolean foundPosition = false;
				for (int j = 0; !foundPosition && j < sortedBins.length; j++) {
					int bi = sortedBins[j].index;
					if (sizes[i] > sortedBins[j].capacity) {
						if (dom.removeValueIfPresent(bi) == false)
							return false;
					} else if (dom.present(bi)) {
						foundPosition = true;
						positions[j].add(i);
					}
				}
				if (!foundPosition) {
					System.out.println("jjjj");
					return x.dom.fail();
				}
				if (dom.size() == 1) {
					bins[dom.uniqueValue()].capacity -= sizes[i];
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

		for (Bin bin : bins)
			if (bin.capacity < 0)
				return x.dom.fail();

		assert Stream.of(sortedBins).allMatch(bin -> bin.capacity >= 0);

		// energetic reasoning
		int cumulatedAvailableCapacities = 0, cumulatedSizes = 0;
		for (int j = sortedBins.length - 1; j >= 0; j--) {
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
				// System.out.println("jjjj2 " + margin);
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
		return true;
	}

}
