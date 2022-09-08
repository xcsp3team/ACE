/*
0 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import static utility.Kit.control;

import java.util.Arrays;
import java.util.stream.IntStream;

import org.xcsp.common.Range;

import constraints.ConstraintGlobal;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagNotAC;
import problem.Problem;
import sets.SetDense;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This constraint BinPacking ensures that we cannot exceed the capacity (limit) of bins where we put various items (of
 * various sizes). The code is still experimental (problems to be tested: BinPacking2.py, NursingWorkload and
 * TestBinpacking from special).
 * 
 * @author Christophe Lecoutre
 */
public abstract class BinPacking extends ConstraintGlobal implements TagNotAC {
	// TODO both subclasses are call filtering-complete? to check and test

	@Override
	public boolean isSatisfiedBy(int[] t) {
		Arrays.fill(sums, 0);
		for (int i = 0; i < t.length; i++)
			sums[scp[i].dom.toIdx(t[i])] += sizes[i];
		for (int i = 0; i < sums.length; i++)
			if (sums[i] > limits[i])
				return false;
		return true;
	}

	/**
	 * The number of items to be put in the bins
	 */
	protected int nItems;

	/**
	 * The number of bins
	 */
	protected int nBins;

	/**
	 * sizes[i] is the size of the ith item
	 */
	protected final int[] sizes;

	/**
	 * limits[j] is the capacity of the jth bin
	 */
	protected final int[] limits;

	/**
	 * A temporary array used when checking values
	 */
	protected final long[] sums;

	public BinPacking(Problem pb, Variable[] scp, int[] sizes, int[] limits) {
		super(pb, scp);
		this.nItems = sizes.length;
		this.nBins = limits.length;
		control(nItems >= 2 && Variable.haveSameDomainType(IntStream.range(0, nItems).mapToObj(i -> scp[i]).toArray(Variable[]::new)));
		control(nBins == scp[0].dom.initSize() && scp[0].dom.initiallyExactly(new Range(0, nBins)));
		// TODO second condition above to be relaxed when possible
		this.sizes = sizes;
		this.limits = limits;
		this.sums = new long[nBins];
		defineKey(sizes, limits);
	}

	public BinPacking(Problem pb, Variable[] scp, int[] sizes, int limit) {
		this(pb, scp, sizes, Kit.repeat(limit, scp[0].dom.initSize()));
	}

	public static final class BinPackingBasic extends BinPacking {

		private final SetDense set;

		public BinPackingBasic(Problem pb, Variable[] scp, int[] sizes, int[] limits) {
			super(pb, scp, sizes, limits);
			this.set = new SetDense(scp.length);
		}

		public BinPackingBasic(Problem pb, Variable[] scp, int[] sizes, int limit) {
			this(pb, scp, sizes, Kit.repeat(limit, scp[0].dom.initSize()));
		}

		@Override
		public boolean runPropagator(Variable x) {
			Arrays.fill(sums, 0);
			set.clear();
			for (int i = 0; i < scp.length; i++) {
				int a = scp[i].dom.size() > 1 ? -1 : scp[i].dom.single();
				if (a != -1)
					sums[a] += sizes[i];
				else
					set.add(i);
			}
			for (int i = 0; i < sums.length; i++)
				if (sums[i] > limits[i])
					return x.dom.fail();
			for (int i = set.limit; i >= 0; i--) {
				int p = set.dense[i];
				Domain dom = scp[p].dom;
				int sizeBefore = dom.size();
				for (int a = dom.first(); a != -1; a = dom.next(a))
					if (sums[a] + sizes[p] > limits[a])
						dom.removeElementary(a);
				if (dom.afterElementaryCalls(sizeBefore) == false)
					return false;
			}
			return true;
		}

	}

	public static class BinPackingEnergetic extends BinPacking implements ObserverOnBacktracksSystematic {

		@Override
		public void afterProblemConstruction(int n) {
			super.afterProblemConstruction(n);
			this.usableBins = new SetSparseReversible(bins.length, n + 1);
		}

		@Override
		public void restoreBefore(int depth) {
			usableBins.restoreLimitAtLevel(depth);
		}

		private static class Bin {
			int index;
			int capacity; // the capacity is updated when possible (when an object is guaranteed to be in it)
			int lost; // only used when reasoning energetically

			void set(int i, int c) {
				this.index = i;
				this.capacity = c;
			}

			@Override
			public String toString() {
				return "(" + index + ":cap=" + capacity + ")";
			}
		}

		/**
		 * The array of possible bins
		 */
		private Bin[] bins;

		/**
		 * The array of bins, sorted according to their current remaining capacities
		 */
		private Bin[] sortedBins;

		/**
		 * fronts[i] is the set of items which are in front of the ith bin (in the ordered sequence of bins) such that i
		 * is the first position where they can be put
		 */
		private SetDense[] fronts;

		private SetSparseReversible usableBins; // set of currently usable bins

		public BinPackingEnergetic(Problem pb, Variable[] scp, int[] sizes, int[] limits) {
			super(pb, scp, sizes, limits);
			this.bins = IntStream.range(0, nBins).mapToObj(i -> new Bin()).toArray(Bin[]::new);
			this.sortedBins = bins.clone();
			this.fronts = IntStream.range(0, nBins).mapToObj(i -> new SetDense(sizes.length)).toArray(SetDense[]::new);
		}

		public BinPackingEnergetic(Problem pb, Variable[] scp, int[] sizes, int limit) {
			this(pb, scp, sizes, Kit.repeat(limit, scp[0].dom.initSize()));
		}

		@Override
		public boolean runPropagator(Variable x) {
			// initialization
			for (int j = 0; j <= usableBins.limit; j++) {
				int i = usableBins.dense[j];
				bins[i].set(i, limits[i]); // the bin is reinitialized with its initial capacity
				sortedBins[j] = bins[i];
			}
			// updating the capacity of bins
			for (int i = 0; i < nItems; i++)
				if (scp[i].dom.size() == 1) {
					bins[scp[i].dom.single()].capacity -= sizes[i]; // the capacity is updated
					// if (bins[scp[i].dom.unique()].capacity < 0) // TODO why it does not work ? because we update
					// useless abandoned bins
					// return x.dom.fail();
				}

			// putting each object in front of the right bin (the first one where it can enter)
			int maxSize = -1;
			int sortLimit = usableBins.limit + 1;
			start: while (true) {
				maxSize = -1;
				Arrays.sort(sortedBins, 0, sortLimit, (b1, b2) -> Integer.compare(b1.capacity, b2.capacity)); // increasing
																												// sort
				if (sortedBins[0].capacity < 0)
					return x.dom.fail(); // TODO 1: moving it earlier (avoid the first sort) ?
				for (SetDense set : fronts) // TODO 2: only clearing from 0 to usableBins.limit ?
					set.clear();
				// for (int ii = futvars.limit; ii >= 0; ii--) {
				// int p = futvars.dense[ii];
				for (int p = 0; p < nItems; p++) { // TODO 3: only iterating over future variables? (but the
													// condition remains)
					Domain dom = scp[p].dom;
					if (dom.size() == 1)
						continue; // because already considered (when reducing the appropriate bin capacity)
					int position = -1;
					for (int j = 0; position == -1 && j <= usableBins.limit; j++) {
						int i = sortedBins[j].index;
						if (sizes[p] > sortedBins[j].capacity) {
							if (dom.removeValueIfPresent(i) == false)
								return false;
						} else if (dom.contains(i)) {
							position = j;
							fronts[j].add(p);
						}
					}
					if (position == -1) {
						return x.dom.fail();
					}
					if (dom.size() == 1) {
						bins[dom.single()].capacity -= sizes[p]; // note that sortedBins has references to bins
						if (bins[dom.single()].capacity < 0)
							return x.dom.fail();
						sortLimit = position + 1; // TODO only inserting rather than sorting ?
						continue start;
					}
					if (sizes[p] > maxSize)
						maxSize = sizes[p];
				}
				break;
			}

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
				sortedBins[j].lost = onyOnePossibleInTheBin ? capacity - max : 0; // local j-lost place
				int lost = sortedBins[j].lost;
				// under certain conditions, we can combine several local lost places
				for (int jj = usableBins.limit; jj > j; jj--) {
					if (min <= sortedBins[jj].lost)
						sortedBins[jj].lost = 0;
					else
						lost += sortedBins[jj].lost;
				}
				// note that even if several bins have the same current capacity, it does not mean that all items
				// are in front of the leftmost one (due to other constraints)

				// margin is a global value computed when reasoning from the jth sorted bin to the rightmost one
				int margin = cumulatedCapacities - lost - cumulatedSizes;
				// the margin is computed from the object of max size (when only one possible)
				if (margin < 0)
					return x.dom.fail();
				if (onyOnePossibleInTheBin && margin - (max - min) < 0) {
					// we can remove some values if the smallest item cannot be put in the bin j
					for (int k = 0; k <= fronts[j].limit; k++) {
						int i = fronts[j].dense[k];
						if (margin - (max - sizes[i]) < 0 && scp[i].dom.removeValueIfPresent(sortedBins[j].index) == false)
							return false;
					}
				}
				// maybe, some items in front of a bin on the left have a size greater than the margin (we can then
				// remove them from bins on the right)
				if (maxSize > margin) {
					for (int left = 0; left < j; left++) {
						if (fronts[left].size() == 0)
							continue;
						for (int k = 0; k <= fronts[left].limit; k++) {
							int p = fronts[left].dense[k];
							int size = sizes[p];
							if (size <= margin)
								continue;
							for (int right = usableBins.limit; right >= j; right--) {
								if (scp[p].dom.removeValueIfPresent(sortedBins[right].index) == false)
									return false;
							}
						}
					}
				}
			}

			// we look for the index of the smallest free item, and also compute the min and max usable bin numbers
			int smallestFreeItem = -1, minUsableBin = Integer.MAX_VALUE, maxUsableBin = -1;
			for (int i = 0; i < nItems; i++) {
				if (scp[i].dom.size() > 1) {
					if (smallestFreeItem == -1)
						smallestFreeItem = i;
					minUsableBin = Math.min(minUsableBin, scp[i].dom.first());
					maxUsableBin = Math.max(maxUsableBin, scp[i].dom.last());
				}
			}

			if (smallestFreeItem == -1)
				return true;

			// we discard bins that are now identified as useless because we cannot even put the smallest item in it
			for (int j = usableBins.limit; j >= 0; j--) {
				// for breaking, we should go from 0 to ..., but removing an element in usableBins could be a pb
				int i = sortedBins[j].index;
				assert usableBins.contains(i);
				if (sortedBins[j].capacity < sizes[smallestFreeItem] || i > maxUsableBin || i < minUsableBin)
					usableBins.remove(i, problem.solver.depth());
			}
			return true;
		}
	}

	public static final class BinPackingEnergeticLoad extends BinPackingEnergetic {

		private final SetDense freeItems;

		@Override
		public final boolean isSatisfiedBy(int[] t) {
			Arrays.fill(sums, 0);
			for (int i = 0; i < nItems; i++)
				sums[scp[i].dom.toIdx(t[i])] += sizes[i];
			for (int i = 0; i < sums.length; i++)
				if (sums[i] != t[nItems + i])
					return false;
			return true;
		}

		private Variable[] loads;

		int cnt = 0;

		@Override
		public boolean runPropagator(Variable x) {
			// we call the super propagator after setting the highest possible limits

			// if (futvars.size() == 0) {
			// int[] t = Stream.of(scp).mapToInt(y -> y.dom.singleValue()).toArray();
			// if (!isSatisfiedBy(t)) {
			// cnt++;
			// System.out.println("bef " + cnt); // pb to fix for java ace GeneralizedBACP-reduced_UD2-gbac.xml
			// // -valh=Bivs
			// TODO other pb : java ace TeamAssignment-data1_6_6.xml -valh=Asgs
			// }
			// }
			for (int i = 0; i < nBins; i++)
				limits[i] = loads[i].dom.lastValue();
			if (super.runPropagator(x) == false)
				return false;

			Arrays.fill(sums, 0);
			freeItems.clear();
			for (int i = 0; i < nItems; i++)
				if (scp[i].dom.size() == 1)
					sums[scp[i].dom.single()] += sizes[i];
				else
					freeItems.add(i);
			for (int i = 0; i < nBins; i++) {
				long currentFill = sums[i];
				if (loads[i].dom.size() == 1) {
					int load = loads[i].dom.singleValue();
					int possibleExtent = 0;
					int minSize = 0;
					for (int k = freeItems.limit; k >= 0; k--) {
						int j = freeItems.dense[k];
						if (scp[j].dom.containsValue(i)) {
							if (currentFill + sizes[j] > load) {
								if (scp[j].dom.removeValue(i) == false)
									return false;
							} else {
								possibleExtent += sizes[j];
								minSize = Math.min(minSize, sizes[j]);
							}
						}
					}
					if (currentFill + possibleExtent < load)
						return x.dom.fail();
					if (currentFill + possibleExtent == load) {
						for (int k = freeItems.limit; k >= 0; k--) {
							int j = freeItems.dense[k];
							if (scp[j].dom.containsValue(i))
								scp[j].dom.reduceTo(i);
						}
					} else if (currentFill + possibleExtent - minSize < load)
						return x.dom.fail();
				} else {
					if (loads[i].dom.removeValuesLT(currentFill) == false)
						return false;
					int loadMin = loads[i].dom.firstValue();
					int loadMax = loads[i].dom.lastValue();
					int possibleExtent = 0;
					for (int k = freeItems.limit; k >= 0; k--) {
						int j = freeItems.dense[k];
						if (scp[j].dom.containsValue(i)) {
							if (currentFill + sizes[j] > loadMax) {
								if (scp[j].dom.removeValue(i) == false)
									return false;
							} else
								possibleExtent += sizes[j];
						}
					}
					if (currentFill + possibleExtent < loadMin)
						return x.dom.fail();
					if (currentFill + possibleExtent == loadMin) {
						for (int k = freeItems.limit; k >= 0; k--) {
							int j = freeItems.dense[k];
							if (scp[j].dom.containsValue(i))
								scp[j].dom.reduceTo(i);
						}
					}
				}
			}
			// if (futvars.size() == 0) {
			// int[] t = Stream.of(scp).mapToInt(y -> y.dom.singleValue()).toArray();
			// if (!isSatisfiedBy(t))
			// System.out.println("after " + cnt); // pb to fix for java ace GeneralizedBACP-reduced_UD2-gbac.xml
			// // -valh=Bivs
			// }
			return true;
		}

		public BinPackingEnergeticLoad(Problem pb, Variable[] list, int[] sizes, Variable[] loads) {
			super(pb, pb.vars(list, loads), sizes, new int[loads.length]);
			control(list.length == sizes.length && nBins == loads.length && scp.length == list.length + loads.length);
			this.loads = loads;
			this.freeItems = new SetDense(nItems);
		}

	}

}
