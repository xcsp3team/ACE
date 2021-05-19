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
import interfaces.Observers.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagNotAC;
import problem.Problem;
import sets.SetSparse;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Variable;

public final class Cumulative extends CtrGlobal implements TagFilteringCompleteAtEachCall, TagNotAC, ObserverBacktrackingSystematic {

	@Override
	public boolean checkValues(int[] tuple) {
		int min = Integer.MAX_VALUE, max = Integer.MIN_VALUE;
		for (int i = 0; i < tuple.length; i++) {
			min = Math.min(min, tuple[i]);
			max = Math.max(max, tuple[i] + widths[i]);
		}
		for (int t = min; t <= max; t++) {
			int sum = 0;
			for (int i = 0; i < tuple.length; i++)
				if (tuple[i] <= t && t < tuple[i] + widths[i])
					sum += heights[i];
			if (sum > limit)
				return false;
		}
		return true;
	}

	@Override
	public void restoreBefore(int depth) {
		relevantTasks.restoreLimitAtLevel(depth);
	}

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.relevantTasks = new SetSparseReversible(scp.length, problem.variables.length + 1);
	}

	private int[] widths;
	private int[] heights;
	private int limit;

	private SetSparse ticks;
	private int[] offsets;

	private Slot[] slots;
	private int nSlots;

	private SetSparseReversible relevantTasks; // currently relevant tasks (called omega in the CP paper)

	private long volume;
	private long margin;

	private HeightReasoner heightReasoner;

	private static class Slot {
		int start, end, height;

		@Override
		public String toString() {
			return "(" + start + "-" + end + ":" + height + ")";
		}
	}

	private class HeightReasoner {
		private int[] sortedPositions; // according to heights

		private int largestHeight;
		private int[] smallestHeights; // up to 3 values

		HeightReasoner() {
			Integer[] t = IntStream.range(0, scp.length).boxed().toArray(Integer[]::new);
			Arrays.sort(t, (i1, i2) -> heights[i1] > heights[i2] ? -1 : heights[i1] < heights[i2] ? 1 : 0);
			this.sortedPositions = Stream.of(t).mapToInt(i -> i).toArray();

			int highest = heights[sortedPositions[0]], lowest = heights[sortedPositions[scp.length - 1]];
			int smallestHeightsLimit = highest - lowest >= 3 ? 3 : highest > lowest ? 2 : 1;
			this.smallestHeights = new int[smallestHeightsLimit];
		}

		private int largestHeightIndex() {
			for (int i = 0; i < sortedPositions.length; i++)
				if (scp[sortedPositions[i]].dom.size() > 1)
					return i;
			return -1;
		}

		private void findSmallestHeights() {
			int cnt = 0;
			for (int i = sortedPositions.length - 1; i >= 0; i--)
				if (scp[sortedPositions[i]].dom.size() > 1) {
					smallestHeights[cnt++] = heights[sortedPositions[i]];
					if (cnt == smallestHeights.length)
						break;
				}
			// if not enough heights, we copy the last one to fill up the array
			for (int k = cnt; k < smallestHeights.length; k++)
				smallestHeights[k] = smallestHeights[cnt - 1];
		}

		private Boolean reason() {
			int largest = largestHeightIndex();
			if (largest == -1)
				return Boolean.TRUE; // because everything is fixed
			findSmallestHeights();
			// reasoning with slots and the largest available height
			int li = sortedPositions[largest];
			largestHeight = heights[li];
			for (int k = nSlots - 1; k >= 0; k--) {
				int gap = limit - slots[k].height;
				if (gap <= largestHeight)
					break;
				int diff = gap - largestHeight;
				if (smallestHeights[0] > diff && margin - diff * (slots[k].end - slots[k].start + 1) < 0)
					if (scp[li].dom.removeValuesInRange(slots[k].start - widths[li] + 1, slots[k].end) == false)
						return Boolean.FALSE;
			}
			// reasoning with slots and the smallest available heights
			int s1 = smallestHeights[0], s2 = smallestHeights.length <= 1 ? s1 : smallestHeights[1], s3 = smallestHeights.length <= 2 ? s2 : smallestHeights[2];
			long currMargin = margin;
			boolean s1Used = false;
			for (int k = 0; k < nSlots; k++) {
				int gap = limit - slots[k].height;
				if (gap == 0)
					continue;
				if (gap >= s3)
					break;
				int lost = gap < s1 ? gap : gap < s2 ? (s1Used ? gap : gap - s1) : (gap < s1 + s2 ? gap - s2 : gap - s1 - s2);
				s1Used = s1 <= gap && gap < s2;
				assert lost >= 0;
				// System.out.println("lost " + lost + " " + (gap < s1) + " " + (gap < s2) + " " + (gap < s3));
				// System.out.println("k== " + k + " " + lost + "sss " + s1 + " " + s2 + " " + s3);
				currMargin -= (slots[k].end - slots[k].start + 1) * lost;
				if (currMargin < 0)
					return Boolean.FALSE;
			}
			return null;
		}
	}

	private int horizon() {
		int min = Integer.MAX_VALUE, max = Integer.MIN_VALUE;
		for (int i = 0; i < scp.length; i++) {
			min = Math.min(min, scp[i].dom.firstValue());
			max = Math.max(max, scp[i].dom.lastValue() + widths[i]);
		}
		return max - min;
	}

	public Cumulative(Problem pb, Variable[] list, int[] widths, int[] heights, int limit) {
		super(pb, list);
		control(list.length > 1 && list.length == widths.length && list.length == heights.length);
		control(Stream.of(list).allMatch(x -> x.dom.firstValue() >= 0));
		this.widths = widths;
		this.heights = heights;
		this.limit = limit;
		int timeline = IntStream.range(0, scp.length).map(i -> scp[i].dom.lastValue() + widths[i]).max().getAsInt() + 1;
		this.ticks = new SetSparse(timeline);
		this.offsets = new int[timeline];
		this.slots = IntStream.range(0, timeline).mapToObj(i -> new Slot()).toArray(Slot[]::new);

		this.heightReasoner = new HeightReasoner();

		this.volume = IntStream.range(0, widths.length).mapToLong(i -> widths[i] * heights[i]).sum();
		this.margin = horizon() * limit - volume;

		System.out.println(this);
	}

	private int mandatoryStart(int i) {
		return scp[i].dom.lastValue();
	}

	private int mandatoryEnd(int i) {
		return scp[i].dom.firstValue() + widths[i];
	}

	private Boolean buildTimeTable() {
		ticks.clear();
		// for (int i = 0; i < scp.length; i++) {
		for (int j = relevantTasks.limit; j >= 0; j--) {
			int i = relevantTasks.dense[j];
			int ms = mandatoryStart(i), me = mandatoryEnd(i);
			if (me <= ms)
				continue; // no mandatory part here
			if (ticks.isPresent(ms) == false) {
				ticks.add(ms);
				offsets[ms] = 0;
			}
			offsets[ms] += heights[i];
			if (ticks.isPresent(me) == false) {
				ticks.add(me);
				offsets[me] = 0;
			}
			offsets[me] -= heights[i];
		}
		if (ticks.size() == 0)
			return Boolean.TRUE;

		int nRelevantTicks = 0;
		for (int i = 0; i <= ticks.limit; i++)
			if (offsets[ticks.dense[i]] != 0) // ticks with offset at 0 are not relevant (and so, are discarded)
				slots[nRelevantTicks++].start = ticks.dense[i];
		Arrays.sort(slots, 0, nRelevantTicks, (t1, t2) -> t1.start < t2.start ? -1 : t1.start > t2.start ? 1 : 0);

		for (int k = 0, height = 0; k < nRelevantTicks - 1; k++) {
			height += offsets[slots[k].start];
			if (height > limit)
				return Boolean.FALSE;
			slots[k].end = slots[k + 1].start;
			slots[k].height = height;
		}
		Arrays.sort(slots, 0, nRelevantTicks - 1, (t1, t2) -> t1.height > t2.height ? -1 : t1.height < t2.height ? 1 : 0);

		nSlots = nRelevantTicks - 1;
		while (slots[nSlots - 1].height == 0)
			nSlots--; // we discard irrelevant slots (those of height 0)
		return null;
	}

	@Override
	/**
	 * The filtering algorithm is mainly based upon "Simple and Scalable Time-Table Filtering for the Cumulative Constraint" by S. Gay, R. Hartert and P.
	 * Schaus. CP 2015: 149-157
	 */
	public boolean runPropagator(Variable x) {
		int depth = problem.solver.depth();
		if (depth == 0) { // we update the margin
			margin = horizon() * limit - volume;
			System.out.println("margin " + margin + " " + horizon() + " " + limit);
			if (margin < 0)
				return false;
		}

		Boolean b = buildTimeTable();
		if (b == Boolean.FALSE)
			return false; // seems better than x.dom.fail()
		if (b == Boolean.TRUE)
			return true;

		b = heightReasoner.reason();
		if (b == Boolean.FALSE)
			return false; // seems better than x.dom.fail()
		if (b == Boolean.TRUE)
			return true;

		// The five next lines can replace the three uncommented first lines following them
		// Variable lastPast = pb.solver.futVars.lastPast();
		// for (int j = 0; j < sortedScpIndexes.length; j++) {
		// int i = sortedScpIndexes[j];
		// if (slots[0].height + heights[i] <= limit)
		// break;

		if (slots[0].height + heightReasoner.largestHeight > limit) { // if there is some hope of filtering
			Variable lastPast = problem.solver.futVars.lastPast();
			for (int i = 0; i < scp.length; i++) {
				if (scp[i].assigned() && scp[i] != lastPast)
					continue;
				int ms = mandatoryStart(i), me = mandatoryEnd(i);
				for (int k = 0; k < nSlots; k++) {
					if (slots[k].height + heights[i] <= limit)
						break;
					assert slots[k].height != 0;
					int rs = slots[k].start, re = slots[k].end;
					if (me <= ms || me <= rs || re <= ms) { // if no mandatory part or if the rectangle and the mandatory parts are disjoint
						if (scp[i].dom.removeValuesInRange(rs - widths[i] + 1, re) == false)
							return false;
					}
					// else something else ?
				}
			}
		}
		// we compute the relevant time bounds: minimum relevant start time and maximum relevant end time from current future variables
		int smin = Integer.MAX_VALUE, emax = Integer.MIN_VALUE;
		for (int j = futvars.limit; j >= 0; j--) {
			int i = futvars.dense[j];
			smin = Math.min(smin, scp[i].dom.firstValue());
			emax = Math.max(emax, scp[i].dom.lastValue() + widths[i]);
		}
		// we update the set of relevant tasks to consider from (smin,emax)
		for (int j = relevantTasks.limit; j >= 0; j--) {
			int i = relevantTasks.dense[j];
			if (scp[i].dom.size() == 1 && (scp[i].dom.lastValue() + widths[i] <= smin || emax <= scp[i].dom.firstValue()))
				relevantTasks.removeAtPosition(j, depth);
		}
		return true;
	}

	public String toString() {
		return "constraint cumulative: " + Kit.join(scp) + " lengths=" + Kit.join(this.widths) + " heights=" + Kit.join(heights) + " limit=" + limit;
	}
}

// int sizeBefdeValue(v);

// if (me <= ms) {
// for (int k = 0; k < m; k++) {
// if (slots[k].height + heights[i] <= limit)
// break;
// if (scp[i].dom.removeValues(TypeConditionOperatorSet.IN, slots[k].start -lengths[i] + 1, slots[k].end) == false)
// return false;
// }
// } else {
// for (int k = 0; k < m; k++) {
// if (slots[k].height + heights[i] <= limit)
// break;
// int rs = slots[k].start, re = slots[k].end;
// if (me <= rs || re <= ms) { // if the rectangle and the mandatory parts are disjoint
// if (scp[i].dom.removeValues(TypeConditionOperatorSet.IN, rs - lengths[i] + 1, re) == false)
// return false;
// } else {
// // if the rectangle and the mandatory part are left-overlapping
// if (rs < ms) {
// assert re > ms;
// if (scp[i].dom.removeValues(TypeConditionOperatorSet.IN, rs, ms) == false)
// return false;
// }
// // if the rectangle and the mandatory part are right-overlapping
// if (me < re) {
// assert rs < me;
// if (scp[i].dom.removeValues(TypeConditionOperatorSet.IN, me, re) == false)
// return false;
// }
// }
// }
// }
