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

public abstract class Cumulative extends CtrGlobal implements TagFilteringCompleteAtEachCall, TagNotAC, ObserverBacktrackingSystematic {

	@Override
	public void restoreBefore(int depth) {
		relevantTasks.restoreLimitAtLevel(depth);
	}

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.relevantTasks = new SetSparseReversible(starts.length, problem.variables.length + 1);
	}

	protected final Variable[] starts; // starting times of tasks
	protected int[] widths;
	protected int[] heights;
	protected int limit;

	protected SetSparse ticks;
	protected int[] offsets;

	protected Slot[] slots;
	protected int nSlots;

	protected SetSparseReversible relevantTasks; // currently relevant tasks (called omega in the CP paper)

	protected long volume;
	protected long margin;

	protected HeightReasoner heightReasoner;

	protected boolean movableHeights;

	private static class Slot {
		int start, end, height;

		@Override
		public String toString() {
			return "(" + start + "-" + end + ":" + height + ")";
		}
	}

	private class HeightReasoner {
		private Integer[] sortedPositions; // according to heights

		private int[] smallestHeights; // up to 3 values

		HeightReasoner() {
			this.sortedPositions = IntStream.range(0, starts.length).boxed().toArray(Integer[]::new);
			if (!movableHeights) {
				Arrays.sort(sortedPositions, (i1, i2) -> heights[i1] > heights[i2] ? -1 : heights[i1] < heights[i2] ? 1 : 0);
				int highest = heights[sortedPositions[0]], lowest = heights[sortedPositions[starts.length - 1]];
				this.smallestHeights = new int[1]; // highest - lowest >= 3 ? 3 : highest > lowest ? 2 : 1];
			} else
				this.smallestHeights = new int[2];
		}

		private int largestHeightIndex() {
			for (int k = 0; k < sortedPositions.length; k++) {
				int i = sortedPositions[k];
				if (starts[i].dom.size() > 1)
					return i;
			}
			return -1;
		}

		private void findSmallestHeights() {
			int cnt = 0;
			for (int k = sortedPositions.length - 1; k >= 0; k--) {
				int i = sortedPositions[k];
				if (starts[i].dom.size() > 1) {
					smallestHeights[cnt++] = heights[i];
					if (cnt == smallestHeights.length)
						break;
				}
			}
			// if not enough heights, we copy the last found one to fill up the array
			for (int k = cnt; k < smallestHeights.length; k++)
				smallestHeights[k] = smallestHeights[cnt - 1];
		}

		private Boolean reason() {
			if (movableHeights)
				Arrays.sort(sortedPositions, (i1, i2) -> heights[i1] > heights[i2] ? -1 : heights[i1] < heights[i2] ? 1 : 0);
			int largest = largestHeightIndex();
			if (largest == -1)
				return Boolean.TRUE; // because everything is fixed
			findSmallestHeights();
			// reasoning with slots and the largest available height
			int largestHeight = heights[largest];
			for (int k = nSlots - 1; k >= 0; k--) {
				int gap = limit - slots[k].height;
				if (gap <= largestHeight)
					break;
				int diff = gap - largestHeight;
				if (smallestHeights[0] > diff && margin - diff * (slots[k].end - slots[k].start + 1) < 0)
					if (starts[largest].dom.removeValuesInRange(slots[k].start - widths[largest] + 1, slots[k].end) == false)
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
		for (int i = 0; i < starts.length; i++) {
			min = Math.min(min, starts[i].dom.firstValue());
			max = Math.max(max, starts[i].dom.lastValue() + widths[i]);
		}
		return max - min;
	}

	public Cumulative(Problem pb, Variable[] list, int[] widths, int[] heights, int limit) {
		super(pb, list);
		control(list.length > 1 && list.length == widths.length && list.length == heights.length);
		control(Stream.of(list).allMatch(x -> x.dom.firstValue() >= 0));
		control(IntStream.of(widths).allMatch(w -> w >= 0) && IntStream.of(heights).allMatch(h -> h >= 0));
		this.starts = list;
		this.widths = widths;
		this.heights = heights;
		this.limit = limit;
		int timeline = IntStream.range(0, starts.length).map(i -> starts[i].dom.lastValue() + widths[i]).max().getAsInt() + 1;
		this.ticks = new SetSparse(timeline);
		this.offsets = new int[timeline];
		this.slots = IntStream.range(0, timeline).mapToObj(i -> new Slot()).toArray(Slot[]::new);

		this.heightReasoner = new HeightReasoner();

		this.volume = IntStream.range(0, widths.length).mapToLong(i -> widths[i] * heights[i]).sum();
		this.margin = horizon() * limit - volume;

		System.out.println(this);
	}

	private int mandatoryStart(int i) {
		return starts[i].dom.lastValue();
	}

	private int mandatoryEnd(int i) {
		return starts[i].dom.firstValue() + widths[i];
	}

	private Boolean buildTimeTable() {
		ticks.clear();
		// for (int i = 0; i < origins.length; i++) {
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
		for (int j = 0; j <= ticks.limit; j++)
			if (offsets[ticks.dense[j]] != 0) // ticks with offset at 0 are not relevant (and so, are discarded)
				slots[nRelevantTicks++].start = ticks.dense[j];
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

	private void updateRelevantTasks() {
		int depth = problem.solver.depth();
		// we compute the relevant time bounds: minimum relevant start time and maximum relevant end time from current future variables
		int smin = Integer.MAX_VALUE, emax = Integer.MIN_VALUE;
		for (int j = futvars.limit; j >= 0; j--) {
			int i = futvars.dense[j];
			smin = Math.min(smin, starts[i].dom.firstValue());
			emax = Math.max(emax, starts[i].dom.lastValue() + widths[i]);
		}
		// we update the set of relevant tasks to consider from (smin,emax)
		for (int j = relevantTasks.limit; j >= 0; j--) {
			int i = relevantTasks.dense[j];
			if (starts[i].dom.size() == 1 && (starts[i].dom.lastValue() + widths[i] <= smin || emax <= starts[i].dom.firstValue()))
				relevantTasks.removeAtPosition(j, depth);
		}
	}

	@Override
	/**
	 * The filtering algorithm is mainly based upon "Simple and Scalable Time-Table Filtering for the Cumulative Constraint" by S. Gay, R. Hartert and P.
	 * Schaus. CP 2015: 149-157
	 */
	public boolean runPropagator(Variable dummy) {
		if (problem.solver.depth() == 0) { // we update the margin
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

		Variable lastPast = problem.solver.futVars.lastPast();
		for (int j = 0; j < starts.length; j++) {
			int i = heightReasoner.sortedPositions[j];
			if (slots[0].height + heights[i] <= limit)
				break;
			if (starts[i].assigned() && starts[i] != lastPast)
				continue;
			int ms = mandatoryStart(i), me = mandatoryEnd(i);
			for (int k = 0; k < nSlots; k++) {
				if (slots[k].height + heights[i] <= limit)
					break;
				assert slots[k].height != 0;
				int rs = slots[k].start, re = slots[k].end;
				if (me <= ms || me <= rs || re <= ms) { // if no mandatory part or if the rectangle and the mandatory parts are disjoint
					if (starts[i].dom.removeValuesInRange(rs - widths[i] + 1, re) == false)
						return false;
				}
				// else something else ?
			}
		}

		updateRelevantTasks();
		return true;
	}

	public String toString() {
		return "constraint cumulative: " + Kit.join(starts) + " lengths=" + Kit.join(this.widths) + " heights=" + Kit.join(heights) + " limit=" + limit;
	}

	public static final class CumulativeCst extends Cumulative {
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

		public CumulativeCst(Problem pb, Variable[] list, int[] widths, int[] heights, int limit) {
			super(pb, list, widths, heights, limit);
		}
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
