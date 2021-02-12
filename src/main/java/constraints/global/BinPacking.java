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
import java.util.stream.LongStream;
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
		return LongStream.of(sums).noneMatch(l -> l > limit);
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
			return "(" + index + "-" + capacity + ")";
		}
	}

	private final int[] sizes;
	private final int limit;

	private Bin[] bins;
	private SetDense[] positions;

	private final long[] sums; // used for checking values

	public BinPacking(Problem pb, Variable[] scp, int[] sizes, int limit) { // TODO to be changed in int[] limits
		super(pb, scp);
		defineKey(Kit.join(sizes) + " " + limit);
		control(scp.length >= 2 && Variable.haveSameDomainType(scp)); // TODO checking that all domains are from 0 to nBins-1

		this.sizes = sizes;
		this.limit = limit;

		int nBins = scp[0].dom.initSize();
		this.bins = IntStream.range(0, nBins).mapToObj(i -> new Bin()).toArray(Bin[]::new);
		this.positions = IntStream.range(0, nBins).mapToObj(i -> new SetDense(scp.length)).toArray(SetDense[]::new);

		this.sums = new long[nBins];
	}

	@Override
	public boolean runPropagator(Variable x) {
		// initialization
		for (int i = 0; i < bins.length; i++)
			bins[i].set(i, limit);
		// updating the capacity of bins
		for (int i = 0; i < scp.length; i++)
			if (scp[i].dom.size() == 1)
				bins[scp[i].dom.uniqueValue()].capacity -= sizes[i];
		// putting each object in front of the right bin (the first one where it can enter)
		start: while (true) {
			Arrays.sort(bins, (b1, b2) -> Integer.compare(b1.capacity, b2.capacity));
			for (SetDense set : positions)
				set.clear();
			for (int i = 0; i < scp.length; i++) {
				Domain dom = scp[i].dom;
				if (dom.size() == 1)
					continue;
				for (int j = 0; j < bins.length; j++) {
					// TODO what if bins[j].index is not in the domain of scp[i]. we have to continue? right?
					if (sizes[i] > bins[j].capacity) {
						if (dom.removeValueIfPresent(bins[j].index) == false)
							return false;
					} else {
						positions[j].add(i);
						break;
					}
				}
				// TODO possibly i has not been added. what to do?
				if (dom.size() == 1) {
					bins[dom.uniqueValue()].capacity -= sizes[i];
					continue start;
				}
			}
			break;
		}
		assert Stream.of(bins).allMatch(bin -> bin.capacity >= 0);

		// reasoning energitically
		int cumulatedAvailableCapacities = 0, cumulatedSizes = 0;
		for (int j = bins.length - 1; j >= 0; j--) {
			int capacity = bins[j].capacity;
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
			if (margin < 0)
				return x.dom.fail();
			if (onyOnePossibleInTheBin && (max - min) > margin) { // we can remove some values
				for (int k = 0; k <= positions[j].limit; k++) {
					int i = positions[j].dense[k];
					if ((max - sizes[i]) > margin && scp[i].dom.removeValueIfPresent(bins[j].index) == false)
						return false;
				}
			}
		}
		return true;
	}

}
