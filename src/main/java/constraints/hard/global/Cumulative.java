/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeConditionOperatorSet;

import constraints.hard.CtrGlobal;
import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACUnguaranteed;
import problem.Problem;
import utility.sets.SetSparse;
import utility.sets.SetSparseReversible;
import variables.Variable;

public final class Cumulative extends CtrGlobal implements TagFilteringCompleteAtEachCall, TagGACUnguaranteed, ObserverBacktrackingSystematic {

	@Override
	public boolean checkValues(int[] tuple) {
		int min = IntStream.of(tuple).min().getAsInt();
		int max = IntStream.range(0, tuple.length).map(i -> tuple[i] + lengths[i]).max().getAsInt();
		return IntStream.rangeClosed(min, max)
				.allMatch(t -> IntStream.range(0, tuple.length).filter(i -> tuple[i] <= t && t < tuple[i] + lengths[i]).map(i -> heights[i]).sum() <= limit);
	}

	@Override
	public void restoreBefore(int depth) {
		omega.restoreLimitAtLevel(depth);
	}

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		this.omega = new SetSparseReversible(scp.length, pb.variables.length + 1);
	}

	private int[] lengths;

	private int[] heights;

	private int limit;

	private SetSparse ticks;

	private int[] offsets;

	private Slot[] slots;

	private int nSlots;

	private SetSparseReversible omega;

	private int[] sortedScpIndexes;

	private static class Slot {
		int start, end, height;

		@Override
		public String toString() {
			return "(" + start + "-" + end + ":" + height + ")";
		}
	}

	public Cumulative(Problem pb, Variable[] list, int[] lengths, int[] heights, int limit) {
		super(pb, list);
		this.lengths = lengths;
		this.heights = heights;
		this.limit = limit;
		int horizon = IntStream.range(0, scp.length).map(i -> scp[i].dom.lastValue() + lengths[i]).max().getAsInt() + 1;
		this.ticks = new SetSparse(horizon);
		this.offsets = new int[horizon];
		this.slots = IntStream.range(0, horizon).mapToObj(i -> new Slot()).toArray(Slot[]::new);

		Integer[] t = IntStream.range(0, scp.length).mapToObj(i -> new Integer(i)).toArray(Integer[]::new);
		Arrays.sort(t, (i1, i2) -> heights[i1] > heights[i2] ? -1 : heights[i1] < heights[i2] ? 1 : 0);
		this.sortedScpIndexes = Stream.of(t).mapToInt(i -> i).toArray();
	}

	private int mandatoryStart(int i) {
		return scp[i].dom.lastValue();
	}

	private int mandatoryEnd(int i) {
		return scp[i].dom.firstValue() + lengths[i];
	}

	private Boolean buildTimeTable() {
		ticks.clear();
		// for (int i = 0; i < scp.length; i++) {
		for (int j = omega.limit; j >= 0; j--) {
			int i = omega.dense[j];
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

		int nbRelevantTicks = 0;
		for (int i = 0; i <= ticks.limit; i++)
			if (offsets[ticks.dense[i]] != 0)
				slots[nbRelevantTicks++].start = ticks.dense[i];
		Arrays.sort(slots, 0, nbRelevantTicks, (t1, t2) -> t1.start < t2.start ? -1 : t1.start > t2.start ? 1 : 0);

		for (int k = 0, h = 0; k < nbRelevantTicks - 1; k++) {
			h += offsets[slots[k].start];
			if (h > limit)
				return Boolean.FALSE;
			slots[k].end = slots[k + 1].start;
			slots[k].height = h;
		}
		Arrays.sort(slots, 0, nbRelevantTicks - 1, (t1, t2) -> t1.height > t2.height ? -1 : t1.height < t2.height ? 1 : 0);

		nSlots = nbRelevantTicks - 1;
		while (slots[nSlots - 1].height == 0)
			nSlots--; // we discard irrelevant slots (those of height 0)
		return null;
	}

	@Override
	public boolean runPropagator(Variable x) {
		Boolean b = buildTimeTable();
		if (b == Boolean.FALSE)
			return x.dom.fail();
		if (b == Boolean.TRUE)
			return true;

		// The five next lines can replace the three first lines following them
		// Variable lastPast = pb.solver.futVars.lastPast();
		// for (int j = 0; j < sortedScpIndexes.length; j++) {
		// int i = sortedScpIndexes[j];
		// if (slots[0].height + heights[i] <= limit)
		// break;

		if (slots[0].height + heights[sortedScpIndexes[0]] > limit) {
			Variable lastPast = pb.solver.futVars.lastPast();
			for (int i = 0; i < scp.length; i++) {
				if (scp[i].isAssigned() && scp[i] != lastPast)
					continue;
				int ms = mandatoryStart(i), me = mandatoryEnd(i);
				for (int k = 0; k < nSlots; k++) {
					if (slots[k].height + heights[i] <= limit)
						break;
					assert slots[k].height != 0;
					int rs = slots[k].start, re = slots[k].end;
					if (me <= ms || me <= rs || re <= ms) { // if no mandatory part or if the rectangle and the mandatory parts are disjoint
						if (scp[i].dom.removeValues(TypeConditionOperatorSet.IN, rs - lengths[i] + 1, re) == false)
							return false;
					} else {
						// something else ?
					}
				}
			}
		}
		int smin = Integer.MAX_VALUE, emax = -1;
		for (int j = futvars.limit; j >= 0; j--) {
			int i = futvars.dense[j];
			if (scp[i].dom.firstValue() < smin)
				smin = scp[i].dom.firstValue();
			if (emax < scp[i].dom.lastValue() + lengths[i])
				emax = scp[i].dom.lastValue() + lengths[i];
		}
		int depth = pb.solver.depth();
		for (int j = omega.limit; j >= 0; j--) {
			int i = omega.dense[j];
			if (scp[i].dom.size() == 1 && (scp[i].dom.lastValue() + lengths[i] <= smin || emax <= scp[i].dom.firstValue()))
				omega.removeAtPosition(j, depth);
		}
		return true;
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
