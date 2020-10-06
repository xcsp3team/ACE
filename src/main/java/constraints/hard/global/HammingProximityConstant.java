/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import static org.xcsp.common.Types.TypeOperatorRel.GT;
import static org.xcsp.common.Types.TypeOperatorRel.LT;

import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import constraints.hard.CtrGlobal;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.TagFilteringPartialAtEachCall;
import problem.Problem;
import utility.Kit;
import utility.sets.SetSparse;
import variables.Variable;
import variables.domains.Domain;

public abstract class HammingProximityConstant extends CtrGlobal implements TagGACGuaranteed {

	protected int[] target;

	protected int k;

	public HammingProximityConstant(Problem pb, Variable[] list, int[] target, int k) {
		super(pb, list);
		this.target = target;
		this.k = k;
		defineKey(Kit.join(target), k);
		Kit.control(0 < k && k < list.length && list.length == target.length);
	}

	@Override
	public int[] defineSymmetryMatching() {
		return IntStream.range(0, target.length).map(i -> Utilities.indexOf(target[i], target) + 1).toArray();
	}

	/**
	 * Use only in a dynamic constraint context (e.g. local branching) when the global consistency of the solver's data is handled.
	 */
	public void setTarget(int[] target) {
		this.target = target;
		Kit.control(this.target.length == target.length);
	}

	/**
	 * Use only in a dynamic constraint context (e.g. local branching) when the global consistency of the solver's data is handled.
	 */
	public void setK(int k) {
		this.k = k;
	}

	// ************************************************************************
	// ***** Constraint HammingProximityConstantLE
	// ************************************************************************

	public static final class HammingProximityConstantLE extends HammingProximityConstant implements TagFilteringCompleteAtEachCall {
		@Override
		public boolean checkValues(int[] t) {
			for (int i = 0, cnt = 0; i < t.length; i++)
				if (t[i] == target[i])
					if (++cnt > k)
						return false;
			return true;
		}

		public HammingProximityConstantLE(Problem pb, Variable[] list, int[] target, int k) {
			super(pb, list, target, k);
		}

		@Override
		public boolean runPropagator(Variable x) {
			int cnt = 0;
			for (int i = 0; i < scp.length; i++)
				if (scp[i].dom.onlyContainsValue(target[i]) && ++cnt > k)
					return scp[i].dom.fail(); // inconsistency detected
			if (cnt == k)
				for (int i = 0; i < scp.length; i++)
					if (scp[i].dom.size() != 1)
						scp[i].dom.removeValue(target[i], false);
			return true;
		}
	}

	// ************************************************************************
	// ***** Constraint HammingProximityConstantGE
	// ************************************************************************

	public static final class HammingProximityConstantGE extends HammingProximityConstant implements TagFilteringPartialAtEachCall {
		@Override
		public boolean checkValues(int[] t) {
			for (int i = 0, cnt = 0; i < t.length; i++)
				if (t[i] == target[i])
					if (++cnt == k)
						return true;
			return false;
		}

		/**
		 * used for storing (k+1) sentinels ; stored values correspond to variable positions (vaps)
		 */
		private SetSparse sentinels;

		public HammingProximityConstantGE(Problem pb, Variable[] list, int[] target, int k) {
			super(pb, list, target, k);
			sentinels = new SetSparse(list.length);
			for (int i = 0; i < k + 1; i++)
				sentinels.add(i); // k+1 sentinels
			Kit.control(controlSentinels());
		}

		@Override
		public boolean runPropagator(Variable x) {
			int px = positionOf(x);
			if (!sentinels.isPresent(px) || x.dom.isPresentValue(target[px]))
				return true;
			// we search for another sentinel
			for (int i = sentinels.limit + 1; i < scp.length; i++) {
				int p = sentinels.dense[i];
				if (scp[p].dom.isPresentValue(target[p])) {
					sentinels.swap(px, p);
					return true;
				}
			}
			// no new sentinel found ; we have to assign all k remaining variables
			for (int i = sentinels.limit; i >= 0; i--) {
				int p = sentinels.dense[i];
				if (p != px && !scp[p].isAssigned() && scp[p].dom.reduceToValue(target[p]) == false)
					return false;
			}
			return true;
		}

		private boolean controlSentinels() {
			return IntStream.rangeClosed(0, sentinels.limit).allMatch(i -> scp[sentinels.dense[i]].dom.isPresentValue(target[sentinels.dense[i]]));
		}
	}

	// ************************************************************************
	// ***** Constraint HammingProximityConstantSumLE
	// ************************************************************************

	public static final class HammingProximityConstantSumLE extends HammingProximityConstant
			implements TagFilteringCompleteAtEachCall, ObserverBacktrackingSystematic {
		@Override
		public boolean checkValues(int[] t) {
			for (int i = 0, sum = 0; i < t.length; i++)
				if ((sum += Math.abs(t[i] - target[i])) > k)
					return false;
			return true;
		}

		@Override
		public void restoreBefore(int depth) {
			for (int i = 0; i < minDist.length; i++)
				minDist[i] = 0;
		}

		/**
		 * Array used during propagation to store at index i minimal possible distance between scp[i] and tuple[i].
		 */
		protected final int[] minDist;

		public HammingProximityConstantSumLE(Problem pb, Variable[] list, int[] target, int k) {
			super(pb, list, target, k);
			this.minDist = new int[target.length];
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			int sumMinDist = 0;
			for (int i = 0; i < scp.length; i++) {
				Domain dom = scp[i].dom;
				if (!dom.isPresentValue(target[i] - minDist[i]) && !dom.isPresentValue(target[i] + minDist[i])) {
					int a = dom.first();
					while (dom.toVal(a) < target[i] && a != -1)
						a = dom.next(a);
					if (a == -1)
						minDist[i] = target[i] - dom.lastValue();
					else
						minDist[i] = dom.size() == 1 ? dom.toVal(a) - target[i] : Math.min(dom.toVal(a) - target[i], target[i] - dom.toVal(dom.prev(a)));
				}
				sumMinDist += minDist[i];
			}
			for (int i = 0; i < scp.length; i++) {
				if (!scp[i].dom.removeValues(LT, target[i] - (k - sumMinDist + minDist[i])))
					return false;
				if (!scp[i].dom.removeValues(GT, target[i] + (k - sumMinDist + minDist[i])))
					return false;
			}
			return true;
		}
	}

}
