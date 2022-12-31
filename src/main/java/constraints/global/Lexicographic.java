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

import java.util.stream.IntStream;

import org.xcsp.common.Types.TypeOperatorRel;
import org.xcsp.common.Utilities;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotSymmetric;
import problem.Problem;
import propagation.AC;
import variables.Domain;
import variables.Variable;

/**
 * This constraint ensures that the tuple formed by the values assigned to a first list is less than (or equal to) the
 * tuple formed by the values assigned to a second list. The filtering algorithm is derived from "Propagation algorithms
 * for lexicographic ordering constraints", Artificial Intelligence, 170(10): 803-834 (2006) by Alan M. Frisch, Brahim
 * Hnich, Zeynep Kiziltan, Ian Miguel, and Toby Walsh. The code below is quite close to the one that can be found in
 * Chapter 12 of "Constraint Networks", ISTE/Wiely (2009) by C. Lecoutre.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Lexicographic extends ConstraintGlobal implements TagAC, TagCallCompleteFiltering, TagNotSymmetric {

	public static Lexicographic buildFrom(Problem pb, Variable[] list1, Variable[] list2, TypeOperatorRel op) {
		control(list1.length == list2.length);
		int[] keep = IntStream.range(0, list1.length).filter(i -> list1[i] != list2[i]).toArray();
		Variable[] safeList1 = keep.length == list1.length ? list1 : IntStream.of(keep).mapToObj(i -> list1[i]).toArray(Variable[]::new);
		Variable[] safeList2 = keep.length == list1.length ? list2 : IntStream.of(keep).mapToObj(i -> list2[i]).toArray(Variable[]::new);
		switch (op) {
		case LT:
			return new LexicographicLT(pb, safeList1, safeList2);
		case LE:
			return new LexicographicLE(pb, safeList1, safeList2);
		case GE:
			return new LexicographicLE(pb, safeList2, safeList1);
		default: // GT
			return new LexicographicLT(pb, safeList2, safeList1);
		}
	}

	public static Lexicographic buildFrom(Problem pb, Variable[] list, int[] limit, TypeOperatorRel op) {
		control(list.length == limit.length);
		switch (op) {
		case LT:
			return new LexicographicCstL(pb, list, limit, true);
		case LE:
			return new LexicographicCstL(pb, list, limit, false);
		case GE:
			return new LexicographicCstG(pb, list, limit, false);
		default: // GT
			return new LexicographicCstG(pb, list, limit, true);
		}
	}

	/**
	 * This field indicates if the ordering between the two lists must be strictly respected; if true then we have to
	 * enforce <= (le), otherwise we have to enforce < (lt)
	 */
	protected final boolean strictOrdering;

	public Lexicographic(Problem pb, Variable[] scp, boolean strictOrdering) {
		super(pb, scp);
		this.strictOrdering = strictOrdering;
		defineKey(strictOrdering); // TODO adding the positions pos1 and pos2? (in case there are several
									// occurrences of the same variable)
	}

	// ************************************************************************
	// ***** Constraints LexicographicVar
	// ************************************************************************

	public static abstract class LexicographicVar extends Lexicographic {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			for (int i = 0; i < half; i++) {
				int v = t[pos1[i]], w = t[pos2[i]];
				if (v < w)
					return true;
				if (v > w)
					return false;
			}
			return !strictOrdering;
		}

		/**
		 * A first list (actually array) of variables
		 */
		private final Variable[] list1;

		/**
		 * A second list (actually array) of variables
		 */
		private final Variable[] list2;

		/**
		 * pos1[i] is the position of the variable list1[i] in the constraint scope
		 */
		private final int[] pos1;

		/**
		 * pos2[i] is the position of the variable list2[i] in the constraint scope
		 */
		private final int[] pos2;

		/**
		 * The size of the lists (half of the scope size if no variable occurs several times)
		 */
		private final int half;

		/**
		 * A time counter used during filtering
		 */
		private int lex_time;

		/**
		 * lex_times[x] gives the time at which the variable (at position) x has been set (pseudo-assigned)
		 */
		private final int[] lex_times;

		/**
		 * lex_vals[x] gives the value of the variable (at position) x set at time lex_times[x]
		 */
		private final int[] lex_vals;

		/**
		 * Build a constraint Lexicographic for the specified problem over the two specified lists of variables
		 * 
		 * @param pb
		 *            the problem to which the constraint is attached
		 * @param list1
		 *            a first list of variables
		 * @param list2
		 *            a second list of variables
		 * @param strictOrdering
		 *            if true, the ordering between formed tuples must be strict
		 */
		public LexicographicVar(Problem pb, Variable[] list1, Variable[] list2, boolean strictOrdering) {
			super(pb, pb.vars(list1, list2), strictOrdering);
			this.half = list1.length;
			this.list1 = list1;
			this.list2 = list2;
			control(1 < half && half == list2.length);
			this.pos1 = IntStream.range(0, half).map(i -> Utilities.indexOf(list1[i], scp)).toArray();
			this.pos2 = IntStream.range(0, half).map(i -> Utilities.indexOf(list2[i], scp)).toArray();
			this.lex_times = new int[scp.length];
			this.lex_vals = new int[scp.length];
		}

		private void set(int p, int v) {
			lex_times[p] = lex_time;
			lex_vals[p] = v;
		}

		private boolean isConsistentPair(int alpha, int v) {
			lex_time++;
			set(pos1[alpha], v);
			set(pos2[alpha], v);
			for (int i = alpha + 1; i < half; i++) {
				int x = pos1[i], y = pos2[i];
				int minx = lex_times[x] == lex_time ? lex_vals[x] : list1[i].dom.firstValue();
				int maxy = lex_times[y] == lex_time ? lex_vals[y] : list2[i].dom.lastValue();
				if (minx < maxy)
					return true;
				if (minx > maxy)
					return false;
				set(x, minx);
				set(y, maxy);
			}
			return !strictOrdering;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			int alpha = 0;
			while (alpha < half) {
				Domain dom1 = list1[alpha].dom, dom2 = list2[alpha].dom;
				if (AC.enforceLE(dom1, dom2) == false) // enforce (AC on) x <= y (list1[alpha] <= list2[alpha])
					return false;
				if (dom1.size() == 1 && dom2.size() == 1) {
					if (dom1.singleValue() < dom2.singleValue())
						return entailed();
					assert dom1.singleValue() == dom2.singleValue();
					alpha++;
				} else {
					int min1 = dom1.firstValue(), min2 = dom2.firstValue();
					assert min1 <= min2;
					if (min1 == min2 && !isConsistentPair(alpha, min1))
						if (dom2.removeValue(min2) == false)
							return false;
					int max1 = dom1.lastValue(), max2 = dom2.lastValue();
					assert max1 <= max2;
					if (max1 == max2 && !isConsistentPair(alpha, max1))
						if (dom1.removeValue(max1) == false)
							return false;
					assert dom1.firstValue() < dom2.lastValue();
					return true;
				}
			}
			assert alpha == half;
			return !strictOrdering;
		}
	}

	public static final class LexicographicLT extends LexicographicVar {
		public LexicographicLT(Problem pb, Variable[] list1, Variable[] list2) {
			super(pb, list1, list2, true);
		}
	}

	public static final class LexicographicLE extends LexicographicVar {
		public LexicographicLE(Problem pb, Variable[] list1, Variable[] list2) {
			super(pb, list1, list2, false);
		}
	}

	// ************************************************************************
	// ***** Constraints LexicographicCST
	// ************************************************************************

	public static abstract class LexicographicCst extends Lexicographic {

		/**
		 * A first list (actually array) of variables
		 */
		protected final Variable[] list;

		/**
		 * The tuple seen as a limit
		 */
		protected final int[] limit;

		/**
		 * The size of the tuples
		 */
		protected final int r;

		/**
		 * Build a constraint Lexicographic for the specified problem over the two specified lists
		 * 
		 * @param pb
		 *            the problem to which the constraint is attached
		 * @param list
		 *            a list of variables
		 * @param limit
		 *            a list of integers
		 * @param strictOrdering
		 *            if true, the ordering between formed tuples must be strict
		 */
		public LexicographicCst(Problem pb, Variable[] list, int[] limit, boolean strictOrdering) {
			super(pb, list, strictOrdering);
			this.list = list;
			this.limit = limit;
			this.r = list.length;
		}
	}

	public static final class LexicographicCstL extends LexicographicCst {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			for (int i = 0; i < r; i++) {
				if (t[i] < limit[i])
					return true;
				if (t[i] > limit[i])
					return false;
			}
			return !strictOrdering;
		}

		public LexicographicCstL(Problem pb, Variable[] list, int[] limit, boolean strictOrdering) {
			super(pb, list, limit, strictOrdering);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			int i = 0;
			while (i < r) {
				Domain dom = list[i].dom;
				if (dom.removeValuesGT(limit[i]) == false)
					return false;
				if (dom.firstValue() < limit[i])
					break;
				assert dom.size() == 1 && dom.singleValue() == limit[i];
				i++;
			}
			if (i == r)
				return strictOrdering ? dummy.dom.fail() : entailed();
			if (list[i].dom.lastValue() < limit[i])
				return entailed();
			// it remains to find a support for (list[i],limit[i])
			int j = i + 1;
			while (j < r) {
				Domain dom = list[j].dom;
				if (dom.firstValue() < limit[j])
					return true;
				if (dom.firstValue() > limit[j])
					return list[i].dom.removeValue(limit[i]);
				j++;
			}
			assert j == r;
			return strictOrdering ? list[i].dom.removeValue(limit[i]) : true;
		}
	}

	public static final class LexicographicCstG extends LexicographicCst {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			for (int i = 0; i < r; i++) {
				if (t[i] > limit[i])
					return true;
				if (t[i] < limit[i])
					return false;
			}
			return !strictOrdering;
		}

		public LexicographicCstG(Problem pb, Variable[] list, int[] limit, boolean strictOrdering) {
			super(pb, list, limit, strictOrdering);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			int i = 0;
			while (i < r) {
				Domain dom = list[i].dom;
				if (dom.removeValuesLT(limit[i]) == false)
					return false;
				if (dom.lastValue() > limit[i])
					break;
				assert dom.size() == 1 && dom.singleValue() == limit[i];
				i++;
			}
			if (i == r)
				return strictOrdering ? dummy.dom.fail() : entailed();
			if (list[i].dom.firstValue() > limit[i])
				return entailed();
			// it remains to find a support for (list[i],limit[i])
			int j = i + 1;
			while (j < r) {
				Domain dom = list[j].dom;
				if (dom.lastValue() > limit[j])
					return true;
				if (dom.lastValue() < limit[j])
					return list[i].dom.removeValue(limit[i]);
				j++;
			}
			assert j == r;
			return strictOrdering ? list[i].dom.removeValue(limit[i]) : true;
		}
	}

}
