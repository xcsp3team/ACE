/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import static org.xcsp.common.Types.TypeOperatorRel.GT;
import static org.xcsp.common.Types.TypeOperatorRel.LT;
import static utility.Kit.control;

import java.util.stream.IntStream;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagNotAC;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * TO BE FINISHED (extending it to limits defined by variables)
 * 
 * @author Christophe Lecoutre
 */
public abstract class Knapsack extends ConstraintGlobal implements TagNotAC {

	private static final long weightedSum(int[] t, int[] coeffs) {
		assert t.length >= coeffs.length;
		long sum = 0;
		for (int i = 0; i < coeffs.length; i++)
			sum += coeffs[i] * t[i];
		return sum;
	}

	@Override
	public boolean isSatisfiedBy(int[] t) {
		return weightedSum(t, weights) <= wlimit && weightedSum(t, profits) >= plimit;
	}

	protected Variable[] list;

	protected final int[] weights;

	protected final int[] profits;

	/**
	 * The widths of tasks; used as working values (either constants or minimal values in variable domains)
	 */
	protected int wlimit;

	/**
	 * heights of tasks; used as working values (either constants or minimal values in variable domains)
	 */
	protected int plimit;

	protected long wmin, wmax;

	protected long pmin, pmax;

	protected final int minWeight, maxWeight;

	protected final int minProfit, maxProfit;

	private final boolean basic;

	public Knapsack(Problem pb, Variable[] scp, Variable[] list, int[] weights, int[] profits) {
		super(pb, scp);
		control(list.length > 1 && list.length == weights.length && list.length == profits.length);
		this.list = list;
		this.weights = weights;
		this.profits = profits;
		this.minWeight = IntStream.of(weights).filter(w -> w > 0).min().getAsInt();
		this.maxWeight = IntStream.of(weights).max().getAsInt();
		this.minProfit = IntStream.of(profits).filter(w -> w > 0).min().getAsInt();
		this.maxProfit = IntStream.of(profits).max().getAsInt();
		control(minWeight > 0 && minProfit > 0); // for the moment
		this.basic = this instanceof KnapsackCst;
		defineKey(weights, wlimit, profits, plimit);
	}

	protected final void recomputeBounds() {
		wmin = wmax = pmin = pmax = 0;
		for (int i = 0; i < list.length; i++) {
			Domain dom = list[i].dom;
			wmin += weights[i] * dom.firstValue();
			wmax += weights[i] * dom.lastValue();
			pmin += profits[i] * dom.firstValue();
			pmax += profits[i] * dom.lastValue();
		}
	}

	@Override
	public boolean runPropagator(Variable event) {
		if (basic)
			recomputeBounds();
		if (wmax <= wlimit && pmin >= plimit)
			return basic ? entail() : true;
		if (wmin > wlimit || pmax < plimit)
			return event == null ? false : event.dom.fail();
		if (wmax > wlimit) { // otherwise nothing to do
			for (int x = 0; x < list.length; x++) {
				Domain dom = scp[x].dom;
				if (dom.size() == 1 || weights[x] == 0)
					continue;
				int wcoeff = weights[x];
				int pcoeff = profits[x];
				wmax -= wcoeff * dom.lastValue();
				pmax -= pcoeff * dom.lastValue();
				long wmini = wmin - wcoeff * dom.firstValue(); // we remove the contribution of the variable we consider
				long pmini = pmin - pcoeff * dom.firstValue();
				dom.removeValues(GT, wlimit - wmini, wcoeff);
				if (profits[x] == 0)
					continue;
				assert dom.size() > 0;
				while (true) {
					int v = dom.lastValue();
					int nPossibleMoves = (int) Math.floor((wlimit - wmini - wcoeff * v) / minWeight);  //1 if 0 present ? why ?
					if ((pmini + nPossibleMoves * maxProfit) + pcoeff * v < plimit) { //
						if (dom.removeValue(v) == false)
							return false;
					} else
						break;
				}
				wmax += wcoeff * dom.lastValue();
				pmax += pcoeff * dom.lastValue();
				if (wmax <= wlimit)
					break;
			}
		}
		if (pmin < plimit) { // otherwise nothing to do
			for (int x = 0; x < list.length; x++) {
				Domain dom = scp[x].dom;
				if (dom.size() == 1 || profits[x] == 0)
					continue;
				int wcoeff = weights[x];
				int pcoeff = profits[x];
				wmin -= wcoeff * dom.firstValue();
				pmin -= pcoeff * dom.firstValue();
				long wmaxi = wmax - wcoeff * dom.lastValue(); // we remove the contribution of the variable we consider
				long pmaxi = pmax - pcoeff * dom.lastValue();
				dom.removeValues(LT, plimit - pmaxi, pcoeff);
				if (weights[x] == 0)
					continue;
				assert dom.size() > 0;
				while (true) {
					int v = dom.firstValue();
					int nPossibleMoves = (int) Math.floor((pmaxi + pcoeff * v - plimit) / minProfit); // 1 if 0 present ? why ?
					if ((wmaxi - nPossibleMoves * maxWeight) + wcoeff * v > wlimit) {
						if (dom.removeValue(v) == false)
							return false;
					} else
						break;
				}
				wmin += wcoeff * dom.firstValue();
				pmin += pcoeff * dom.firstValue();
				if (pmin >= plimit)
					break;
			}
		}
		return true;
	}

	/**********************************************************************************************
	 * The basic variant, with only constants as limits
	 *********************************************************************************************/

	public static final class KnapsackCst extends Knapsack {

		public KnapsackCst(Problem pb, Variable[] list, int[] weights, int wlimit, int[] profits, int plimit) {
			super(pb, list, list, weights, profits);
			this.wlimit = wlimit;
			this.plimit = plimit;
		}
	}

	/**********************************************************************************************
	 * The other variants, depending on the fact that limits are constants or variables
	 *********************************************************************************************/

	public static abstract class KnapsackVar extends Knapsack {

		protected Variable varwlimit, varplimit;

		public KnapsackVar(Problem pb, Variable[] scp, Variable[] list, int[] weights, Variable wlimit, int[] profits, Variable plimit) {
			super(pb, scp, list, weights, profits);
			this.varwlimit = wlimit; // possibly null
			this.varplimit = plimit; // possibly null
		}
	}

	public final static class KnapsackVarW extends KnapsackVar {
		@Override
		public boolean isSatisfiedBy(int[] t) {
			return weightedSum(t, weights) <= t[scp.length - 1] && weightedSum(t, profits) >= plimit;
		}

		public KnapsackVarW(Problem pb, Variable[] list, int[] weights, Variable wlimit, int[] profits, int plimit) {
			super(pb, pb.vars(list, wlimit, plimit), list, weights, wlimit, profits, null);
			this.plimit = plimit;
		}

		@Override
		public boolean runPropagator(Variable event) {
			recomputeBounds();
			if (varwlimit.dom.removeValuesLT(wmin) == false)
				return false;
			wlimit = varwlimit.dom.lastValue();
			return super.runPropagator(event);
		}
	}

	public final static class KnapsackVarP extends KnapsackVar {
		@Override
		public boolean isSatisfiedBy(int[] t) {
			return weightedSum(t, weights) <= wlimit && weightedSum(t, profits) >= t[scp.length - 1];
		}

		public KnapsackVarP(Problem pb, Variable[] list, int[] weights, int wlimit, int[] profits, Variable plimit) {
			super(pb, pb.vars(list, wlimit, plimit), list, weights, null, profits, plimit);
			this.wlimit = wlimit;
		}

		@Override
		public boolean runPropagator(Variable event) {
			recomputeBounds();
			if (varplimit.dom.removeValuesGT(pmax) == false)
				return false;
			plimit = varplimit.dom.firstValue();
			return super.runPropagator(event);
		}
	}

	public final static class KnapsackVarWP extends KnapsackVar {
		@Override
		public boolean isSatisfiedBy(int[] t) {
			return weightedSum(t, weights) <= t[scp.length - 2] && weightedSum(t, profits) >= t[scp.length - 1];
		}

		public KnapsackVarWP(Problem pb, Variable[] list, int[] weights, Variable wlimit, int[] profits, Variable plimit) {
			super(pb, pb.vars(list, wlimit, plimit), list, weights, wlimit, profits, plimit);
		}

		@Override
		public boolean runPropagator(Variable event) {
			recomputeBounds();
			if (varwlimit.dom.removeValuesLT(wmin) == false || varplimit.dom.removeValuesGT(pmax) == false)
				return false;
			wlimit = varwlimit.dom.lastValue();
			plimit = varplimit.dom.firstValue();
			return super.runPropagator(event);
		}
	}

}
