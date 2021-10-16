/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
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
import java.util.stream.Stream;

import constraints.ConstraintGlobal;
import constraints.global.Cumulative.TimetableReasoner.Slot;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import problem.Problem;
import sets.SetSparse;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Variable;

/**
 * The constraint Cumulative is useful when a resource of limited quantity must be shared for achieving several tasks.
 * The constraint Cumulative enforces that at each point in time, the cumulated height of tasks that overlap that point,
 * does not exceed a specified limit. For example, in a scheduling context where several tasks require some specific
 * quantities of a single resource, the cumulative constraint imposes that a strict limit on the total consumption of
 * the resource is never exceeded at each point of a time line.
 * 
 * So, the context is to manage a collection of tasks, each one being described by 3 attributes: its starting time, its
 * width (length or duration), and its height (resource consumption).
 * 
 * @author Christophe Lecoutre
 */
public abstract class Cumulative extends ConstraintGlobal implements TagNotAC, TagCallCompleteFiltering, ObserverOnBacktracksSystematic {

	/**********************************************************************************************
	 * Implementing interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction(int n) {
		super.afterProblemConstruction(n);
		timetableReasoner.relevantTasks = new SetSparseReversible(nTasks, n + 1);
	}

	@Override
	public void restoreBefore(int depth) {
		timetableReasoner.relevantTasks.restoreLimitAtLevel(depth);
	}

	/**********************************************************************************************
	 * Two inner classes for reasoning
	 *********************************************************************************************/

	/**
	 * Filtering mainly based on "Simple and Scalable Time-Table Filtering for the Cumulative Constraint", CP 2015:
	 * 149-157, by S. Gay, R. Hartert and P. Schaus.
	 */
	class TimetableReasoner {
		class Slot {
			int start, end, height;

			int width() {
				return end - start + 1;
			}

			@Override
			public String toString() {
				return "(" + start + "-" + end + ":" + height + ")";
			}
		}

		private SetSparseReversible relevantTasks; // currently relevant tasks (called omega in the CP paper)

		private Slot[] slots;
		private int nSlots;

		private SetSparse ticks; // intermediary structure used when building slots
		private int[] offsets; // intermediary structure used when building slots

		private TimetableReasoner() {
			int timeline = IntStream.range(0, nTasks).map(i -> starts[i].dom.lastValue() + maxWidth(i)).max().getAsInt() + 1;
			this.slots = IntStream.range(0, timeline).mapToObj(i -> new Slot()).toArray(Slot[]::new);
			this.ticks = new SetSparse(timeline);
			this.offsets = new int[timeline];
		}

		private int mandatoryStart(int i) {
			return starts[i].dom.lastValue();
		}

		private int mandatoryEnd(int i) {
			return starts[i].dom.firstValue() + wwidths[i];
		}

		private Boolean buildSlots() { // so, building the timetable
			ticks.clear();
			// for (int i = 0; i < origins.length; i++) {
			for (int j = relevantTasks.limit; j >= 0; j--) {
				int i = relevantTasks.dense[j];
				int ms = mandatoryStart(i), me = mandatoryEnd(i);
				if (me <= ms)
					continue; // no mandatory part here
				if (ticks.contains(ms) == false) {
					ticks.add(ms);
					offsets[ms] = 0;
				}
				offsets[ms] += wheights[i];
				if (ticks.contains(me) == false) {
					ticks.add(me);
					offsets[me] = 0;
				}
				offsets[me] -= wheights[i];
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
			// we compute the relevant time bounds: minimum relevant start time and maximum relevant end time from
			// current future variables
			int smin = Integer.MAX_VALUE, emax = Integer.MIN_VALUE;
			for (int j = futvars.limit; j >= 0; j--) {
				int i = futvars.dense[j];
				smin = Math.min(smin, starts[i].dom.firstValue());
				emax = Math.max(emax, starts[i].dom.lastValue() + maxWidth(i));
			}
			// we update the set of relevant tasks to consider from (smin,emax)
			for (int j = relevantTasks.limit; j >= 0; j--) {
				int i = relevantTasks.dense[j];
				if (starts[i].dom.size() == 1 && (starts[i].dom.lastValue() + maxWidth(i) <= smin || emax <= starts[i].dom.firstValue()))
					relevantTasks.removeAtPosition(j, depth);
			}
		}

		private boolean filter() {
			Variable lastPast = problem.solver.futVars.lastPast();
			for (int j = 0; j < nTasks; j++) {
				int i = energeticReasoner.sortedTasks[j];
				if (slots[0].height + wheights[i] <= limit)
					break;
				if (starts[i].assigned() && starts[i] != lastPast)
					continue;
				int ms = mandatoryStart(i), me = mandatoryEnd(i);
				for (int k = 0; k < nSlots; k++) {
					if (slots[k].height + wheights[i] <= limit)
						break;
					assert slots[k].height != 0;
					int rs = slots[k].start, re = slots[k].end;
					if (me <= ms || me <= rs || re <= ms) { // if no mandatory part or if the rectangle and the
															// mandatory parts are disjoint
						if (starts[i].dom.removeValuesInRange(rs - wwidths[i] + 1, re) == false)
							return false;
					} // else something else ?
				}
			}
			updateRelevantTasks();
			return true;
		}
	}

	/**
	 * Filtering based on a form of energetic reasoning
	 */
	class EnergeticReasoner {
		private Integer[] sortedTasks; // according to heights

		private int[] smallestHeights; // up to 3 values

		private EnergeticReasoner() {
			this.sortedTasks = IntStream.range(0, nTasks).boxed().toArray(Integer[]::new);
			if (!movableHeights) {
				Arrays.sort(sortedTasks, (i1, i2) -> wheights[i1] > wheights[i2] ? -1 : wheights[i1] < wheights[i2] ? 1 : 0);
				int highest = wheights[sortedTasks[0]], lowest = wheights[sortedTasks[nTasks - 1]];
				this.smallestHeights = new int[1]; // highest - lowest >= 3 ? 3 : highest > lowest ? 2 : 1];
			} else
				this.smallestHeights = new int[2];
		}

		private int largestHeightIndex() {
			for (int k = 0; k < sortedTasks.length; k++) {
				int i = sortedTasks[k];
				if (starts[i].dom.size() > 1)
					return i;
			}
			return -1;
		}

		private void findSmallestHeights() {
			int cnt = 0;
			for (int k = sortedTasks.length - 1; k >= 0; k--) {
				int i = sortedTasks[k];
				if (starts[i].dom.size() > 1) {
					smallestHeights[cnt++] = wheights[i];
					if (cnt == smallestHeights.length)
						break;
				}
			}
			// if not enough heights, we copy the last found one to fill up the array
			for (int k = cnt; k < smallestHeights.length; k++)
				smallestHeights[k] = smallestHeights[cnt - 1];
		}

		private Boolean filter() {
			if (movableHeights)
				Arrays.sort(sortedTasks, (i1, i2) -> wheights[i1] > wheights[i2] ? -1 : wheights[i1] < wheights[i2] ? 1 : 0);
			int largest = largestHeightIndex();
			if (largest == -1)
				return Boolean.TRUE; // because everything is fixed
			findSmallestHeights();
			// reasoning with slots and the largest available height
			int nSlots = timetableReasoner.nSlots;
			int largestHeight = wheights[largest];
			for (int k = nSlots - 1; k >= 0; k--) {
				Slot slot = timetableReasoner.slots[k];
				int gap = limit - slot.height;
				if (gap <= largestHeight)
					break;
				int diff = gap - largestHeight;
				if (smallestHeights[0] > diff && margin - diff * slot.width() < 0)
					if (starts[largest].dom.removeValuesInRange(slot.start - wwidths[largest] + 1, slot.end) == false)
						return Boolean.FALSE;
			}
			// reasoning with slots and the smallest available heights
			int s1 = smallestHeights[0], s2 = smallestHeights.length <= 1 ? s1 : smallestHeights[1], s3 = smallestHeights.length <= 2 ? s2 : smallestHeights[2];
			long currMargin = margin;
			boolean s1Used = false;
			for (int k = 0; k < nSlots; k++) {
				Slot slot = timetableReasoner.slots[k];
				int gap = limit - slot.height;
				if (gap == 0)
					continue;
				if (gap >= s3)
					break;
				int lost = gap < s1 ? gap : gap < s2 ? (s1Used ? gap : gap - s1) : (gap < s1 + s2 ? gap - s2 : gap - s1 - s2);
				s1Used = s1 <= gap && gap < s2;
				assert lost >= 0;
				// System.out.println("lost " + lost + " " + (gap < s1) + " " + (gap < s2) + " " + (gap < s3));
				// System.out.println("k== " + k + " " + lost + "sss " + s1 + " " + s2 + " " + s3);
				currMargin -= slot.width() * lost;
				if (currMargin < 0)
					return Boolean.FALSE;
			}
			return null;
		}
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	@Override
	public boolean isSatisfiedBy(int[] tuple) {
		int wgap = !movableWidths ? -1 : nTasks;
		int hgap = !movableHeights ? -1 : this instanceof CumulativeVarH ? nTasks : nTasks * 2;
		int min = Integer.MAX_VALUE, max = Integer.MIN_VALUE;
		for (int i = 0; i < nTasks; i++) {
			min = Math.min(min, tuple[i]);
			max = Math.max(max, tuple[i] + (wgap == -1 ? wwidths[i] : tuple[wgap + i]));
		}
		for (int t = min; t <= max; t++) {
			int sum = 0;
			for (int i = 0; i < nTasks; i++)
				if (tuple[i] <= t && t < tuple[i] + (wgap == -1 ? wwidths[i] : tuple[wgap + i]))
					sum += (hgap == -1 ? wheights[i] : tuple[hgap + i]);
			if (sum > limit)
				return false;
		}
		return true;
	}

	/**
	 * The number of tasks
	 */
	protected final int nTasks;

	/**
	 * starts[i] gives the starting time of the ith task
	 */
	protected final Variable[] starts;

	/**
	 * The widths of tasks; used as working values (either constants or minimal values in variable domains)
	 */
	protected int[] wwidths;

	/**
	 * heights of tasks; used as working values (either constants or minimal values in variable domains)
	 */
	protected int[] wheights;

	/**
	 * indicates if widths are given by variables (and not constants)
	 */
	protected boolean movableWidths;

	/**
	 * indicates if heights are given by variables (and not constants)
	 */
	protected boolean movableHeights;

	/**
	 * Cumulative limit
	 */
	protected int limit;

	/**
	 * The object that allows us to reasoning from a timetable
	 */
	protected TimetableReasoner timetableReasoner;

	/**
	 * The object that allows us to reason energetically
	 */
	protected EnergeticReasoner energeticReasoner;

	/**
	 * The current margin (in term of volume) that we globally have
	 */
	protected long margin;

	/**
	 * Returns the maximal possible width of the ith task
	 * 
	 * @param i
	 *            the index of a task
	 * @return the maximal possible width of the ith task
	 */
	protected int maxWidth(int i) {
		return wwidths[i];
	}

	/**
	 * Returns the maximal possible height of the ith task
	 * 
	 * @param i
	 *            the index of a task
	 * @return the maximal possible height of the ith task
	 */
	protected int maxHeight(int i) {
		return wheights[i];
	}

	/**
	 * Returns the (minimal) volume occupied by all tasks
	 */
	protected long tasksVolume() {
		long sum = 0;
		for (int i = 0; i < nTasks; i++)
			sum += wwidths[i] * wheights[i]; // correct because we always store the minimal values in these arrays
		return sum;
	}

	/**
	 * Returns the horizon, i.e. the maximal length of the time line that can be used by the tasks
	 */
	private int horizon() {
		int min = Integer.MAX_VALUE, max = Integer.MIN_VALUE;
		for (int i = 0; i < nTasks; i++) {
			min = Math.min(min, starts[i].dom.firstValue());
			max = Math.max(max, starts[i].dom.lastValue() + maxWidth(i));
		}
		return max - min;
	}

	public Cumulative(Problem pb, Variable[] scp, Variable[] starts, int[] widths, int[] heights, int limit) {
		super(pb, scp);
		control(starts.length > 1 && Stream.of(starts).allMatch(x -> x.dom.firstValue() >= 0));
		this.nTasks = starts.length;
		this.starts = starts;
		this.movableWidths = widths == null;
		this.wwidths = movableWidths ? new int[nTasks] : widths;
		this.movableHeights = heights == null;
		this.wheights = movableHeights ? new int[nTasks] : heights;
		this.limit = limit;
		this.timetableReasoner = new TimetableReasoner();
		this.energeticReasoner = new EnergeticReasoner();
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		long volume = this instanceof CumulativeCst ? ((CumulativeCst) this).volume : tasksVolume();
		this.margin = horizon() * limit - volume;
		if (margin < 0) { // it seems that we cannot limit (only use) this test at depth 0
			System.out.println("margin " + margin + " " + horizon() + " " + limit);
			return false;
		}

		Boolean b = timetableReasoner.buildSlots();
		if (b == Boolean.FALSE)
			return false; // seems better than x.dom.fail()
		if (b == Boolean.TRUE)
			return true;

		b = energeticReasoner.filter();
		if (b == Boolean.FALSE)
			return false; // seems better than x.dom.fail()
		if (b == Boolean.TRUE)
			return true;

		return timetableReasoner.filter();
	}

	@Override
	public String toString() {
		return "constraint cumulative: " + Kit.join(starts) + " lengths=" + Kit.join(this.wwidths) + " heights=" + Kit.join(wheights) + " limit=" + limit;
	}

	/**********************************************************************************************
	 * The four variants, depending on the fact that some parameters are constants or variables
	 *********************************************************************************************/

	public static final class CumulativeCst extends Cumulative {
		long volume;

		public CumulativeCst(Problem pb, Variable[] starts, int[] widths, int[] heights, int limit) {
			super(pb, starts, starts, widths, heights, limit);
			control(widths.length == nTasks && heights.length == nTasks);
			control(IntStream.of(widths).allMatch(w -> w >= 0) && IntStream.of(heights).allMatch(h -> h >= 0));
			this.volume = tasksVolume();
		}
	}

	// TO FINALIZE
	public static final class CumulativeVarW extends Cumulative {

		Variable[] widths;

		@Override
		protected int maxWidth(int i) {
			return widths[i].dom.lastValue();
		}

		public CumulativeVarW(Problem pb, Variable[] starts, Variable[] widths, int[] heights, int limit) {
			super(pb, pb.vars(starts, widths), starts, null, heights, limit);
			this.widths = widths;
			control(scp.length == 2 * nTasks && widths.length == nTasks && heights.length == nTasks);
			control(Stream.of(widths).allMatch(x -> x.dom.firstValue() >= 0) && IntStream.of(heights).allMatch(h -> h >= 0));
		}

	}

	// TO TEST
	public static final class CumulativeVarH extends Cumulative {

		Variable[] heights;

		@Override
		protected int maxHeight(int i) {
			return heights[i].dom.lastValue();
		}

		public CumulativeVarH(Problem pb, Variable[] starts, int[] widths, Variable[] heights, int limit) {
			super(pb, pb.vars(starts, heights), starts, widths, null, limit);
			this.heights = heights;
			control(scp.length == 2 * nTasks && widths.length == nTasks && heights.length == nTasks);
			control(IntStream.of(widths).allMatch(h -> h >= 0) && Stream.of(heights).allMatch(x -> x.dom.firstValue() >= 0));
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			for (int i = 0; i < nTasks; i++)
				wheights[i] = heights[i].dom.firstValue();
			if (super.runPropagator(dummy) == false)
				return false;
			for (int i = 0; i < nTasks; i++) {
				if (starts[i].dom.size() == 1 && heights[i].dom.size() > 1) {
					int start = starts[i].dom.singleValue();
					int increase = heights[i].dom.lastValue() - heights[i].dom.firstValue();
					for (int k = 0; k < timetableReasoner.nSlots; k++) {
						Slot slot = timetableReasoner.slots[k];
						int surplus = slot.height + increase - limit;
						if (surplus <= 0)
							break;
						if (!(start + wwidths[i] <= slot.start || slot.end <= start)) // if overlapping
							heights[i].dom.removeValuesGT(heights[i].dom.lastValue() - surplus); // no possible conflict
					}
				}
			}
			return true;
		}
	}

	// TO FINALIZE
	public static final class CumulativeVarWH extends Cumulative {

		Variable[] widths;
		Variable[] heights;

		@Override
		protected int maxWidth(int i) {
			return widths[i].dom.lastValue();
		}

		@Override
		protected int maxHeight(int i) {
			return heights[i].dom.lastValue();
		}

		public CumulativeVarWH(Problem pb, Variable[] starts, Variable[] widths, Variable[] heights, int limit) {
			super(pb, pb.vars(starts, widths, heights), starts, null, null, limit);
			this.widths = widths;
			this.heights = heights;
			control(scp.length == 3 * nTasks && widths.length == nTasks && heights.length == nTasks);
			control(Stream.of(widths).allMatch(x -> x.dom.firstValue() >= 0) && Stream.of(heights).allMatch(x -> x.dom.firstValue() >= 0));
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
