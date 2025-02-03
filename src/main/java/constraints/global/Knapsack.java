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

import static org.xcsp.common.Types.TypeOperatorRel.GT;
import static org.xcsp.common.Types.TypeOperatorRel.LT;
import static utility.Kit.control;

import java.util.stream.IntStream;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagCallCompleteFiltering;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * TO BE FINISHED (extending it to limits defined by variables)
 * 
 * @author Christophe Lecoutre
 */
public final class Knapsack extends ConstraintGlobal implements TagCallCompleteFiltering {

	@Override
	public boolean isSatisfiedBy(int[] t) {

		// TODO

		return true;

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

	/**
	 * indicates if wlimit is given by a variable (and not a constant)
	 */
	protected boolean movableWlimit;

	/**
	 * indicates if plimit is given by a variable (and not a constant)
	 */
	protected boolean movablePlimit;

	protected long wmin;

	protected long wmax;

	protected long pmin;

	protected long pmax;

	protected final int minWeight, maxWeight, minProfit, maxProfit;

	public Knapsack(Problem pb, Variable[] list, int[] weights, int wlimit, int[] profits, int plimit) {
		super(pb, list);
		control(list.length > 1 && list.length == weights.length && list.length == profits.length);
		this.list = list;
		this.weights = weights;
		this.profits = profits;
		this.wlimit = wlimit;
		this.plimit = plimit;
		this.minWeight = IntStream.of(weights).min().getAsInt();
		this.maxWeight = IntStream.of(weights).max().getAsInt();
		this.minProfit = IntStream.of(profits).min().getAsInt();
		this.maxProfit = IntStream.of(profits).max().getAsInt();
		control(minWeight > 0 && minProfit > 0); // for the moment
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
		recomputeBounds();
		if (wmax <= wlimit && pmin >= plimit)
			return entail();
		if (wmin > wlimit || pmax < plimit)
			return event == null ? false : event.dom.fail();
		if (wmax > wlimit) { // otherwise nothing to do
			for (int i = futvars.limit; i >= 0; i--) {
				int x = futvars.dense[i];
				Domain dom = scp[x].dom;
				if (dom.size() == 1)
					continue;
				int wcoeff = weights[x];
				int pcoeff = profits[x];
				wmax -= wcoeff * dom.lastValue();
				pmax -= pcoeff * dom.lastValue();
				long wmini = wmin - wcoeff * dom.firstValue(); // we remove the contribution of the variable we consider
				long pmini = pmin - pcoeff * dom.firstValue();
				dom.removeValues(GT, wlimit - wmini, wcoeff);
				assert dom.size() > 0;
				while (true) {
					int v = dom.lastValue();
					int nPossibleMoves = (int) Math.floor((wlimit - wmini - wcoeff * v) / minWeight);
					if (pmini + pcoeff * v + nPossibleMoves * maxProfit < plimit) {
						if (dom.removeValue(v) == false)
							return false;
					} else
						break;
				}
				wmax += wcoeff * dom.lastValue();
				pmax += wcoeff * dom.lastValue();
				if (wmax <= wlimit)
					break;
			}
		}
		if (pmin < plimit) { // otherwise nothing to do
			for (int i = futvars.limit; i >= 0; i--) {
				int x = futvars.dense[i];
				Domain dom = scp[x].dom;
				if (dom.size() == 1)
					continue;
				int wcoeff = weights[x];
				int pcoeff = profits[x];
				wmin -= wcoeff * dom.firstValue();
				pmin -= pcoeff * dom.firstValue();
				long wmaxi = wmax - wcoeff * dom.lastValue(); // we remove the contribution of the variable we consider
				long pmaxi = pmax - pcoeff * dom.lastValue();
				dom.removeValues(LT, plimit - pmaxi, pcoeff);
				assert dom.size() > 0;
				while (true) {
					int v = dom.firstValue();
					int nPossibleMoves = (int) Math.floor((pmaxi + pcoeff * v - plimit) / minProfit);
					if (wmaxi + wcoeff * v + nPossibleMoves * maxWeight > wlimit) {
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

}
