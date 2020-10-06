/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import org.xcsp.common.Types.TypeOperatorRel;

import constraints.hard.CtrGlobal;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagUnsymmetric;
import problem.Problem;
import variables.Variable;
import variables.domains.Domain;

public abstract class Lexicographic extends CtrGlobal implements TagUnsymmetric, TagFilteringCompleteAtEachCall, TagGACGuaranteed {

	public static Lexicographic buildFrom(Problem pb, Variable[] list1, Variable[] list2, TypeOperatorRel op) {
		switch (op) {
		case LT:
			return new LexicographicLT(pb, list1, list2);
		case LE:
			return new LexicographicLE(pb, list1, list2);
		case GE:
			return new LexicographicLE(pb, list2, list1);
		default: // GT
			return new LexicographicLT(pb, list2, list1);
		}
	}

	@Override
	public boolean checkValues(int[] t) {
		for (int i = 0; i < half; i++) {
			int v = t[positionOf(list1[i])], w = t[positionOf(list2[i])];
			if (v < w)
				return true;
			if (v > w)
				return false;
		}
		return !strictOrdering;
	}

	private final Variable[] list1, list2;
	private final int half;
	private final boolean strictOrdering; // If true then <= (le) else < (lt)

	private final int[] times; // times[x] gives the time at which the variable (at position) x has been set (pseudo-assigned)
	private final int[] vals; // vals[x] gives the value of the variable (at position) x set at time times[x]

	private int alpha;
	private int time;

	public Lexicographic(Problem pb, Variable[] list1, Variable[] list2, boolean strictOrdering) {
		super(pb, pb.distinct(pb.vars(list1, list2)));
		assert list1.length == list2.length;
		this.list1 = list1;
		this.list2 = list2;
		this.half = list1.length;
		this.strictOrdering = strictOrdering;
		this.times = new int[scp.length];
		this.vals = new int[scp.length];
		defineKey(strictOrdering);
	}

	private void set(int p, int v) {
		times[p] = time;
		vals[p] = v;
	}

	private boolean isConsistentPair(Variable x, int v, Variable y, int w) {
		time++;
		set(positionOf(x), v);
		set(positionOf(y), w);
		for (int i = alpha + 1; i < half; i++) {
			int p1 = positionOf(list1[i]), p2 = positionOf(list2[i]);
			int min1 = times[p1] == time ? vals[p1] : list1[i].dom.firstValue();
			int max2 = times[p2] == time ? vals[p2] : list2[i].dom.lastValue();
			if (min1 < max2)
				return true;
			if (min1 > max2)
				return false;
			set(p1, min1);
			set(p2, max2);
		}
		return !strictOrdering;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		alpha = 0;
		while (alpha < half) {
			Domain dom1 = list1[alpha].dom, dom2 = list2[alpha].dom;
			if (dom1.removeValuesGreaterThan(dom2.lastValue()) == false || dom2.removeValuesLessThan(dom1.firstValue()) == false) // establishAC
				return false;
			if (dom1.size() == 1 && dom2.size() == 1 && dom1.firstValue() == dom2.firstValue())
				alpha++;
			else
				break;
		}
		if (alpha >= half)
			return !strictOrdering;
		Domain dom1 = list1[alpha].dom, dom2 = list2[alpha].dom;
		int min1 = dom1.firstValue(), min2 = dom2.firstValue();
		assert min1 <= min2;
		if (min1 == min2 && !isConsistentPair(list1[alpha], min1, list2[alpha], min2))
			if (dom2.removeValue(min2, false) == false)
				return false;
		int max1 = dom1.lastValue(), max2 = dom2.lastValue();
		assert max1 <= max2;
		if (max1 == max2 && !isConsistentPair(list1[alpha], max1, list2[alpha], max2))
			if (dom1.removeValue(max1, false) == false)
				return false;
		assert dom1.firstValue() < dom2.lastValue();
		return true;
	}

	// ************************************************************************
	// ***** Constraint LexicographicLT
	// ************************************************************************

	public static final class LexicographicLT extends Lexicographic {
		public LexicographicLT(Problem pb, Variable[] list1, Variable[] list2) {
			super(pb, list1, list2, true);
		}
	}

	// ************************************************************************
	// ***** Constraint LexicographicLE
	// ************************************************************************

	public static final class LexicographicLE extends Lexicographic {
		public LexicographicLE(Problem pb, Variable[] list1, Variable[] list2) {
			super(pb, list1, list2, false);
		}
	}
}
