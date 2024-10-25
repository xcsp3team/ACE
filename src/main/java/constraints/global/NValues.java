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
import java.util.HashSet;
import java.util.Set;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.Types.TypeConditionOperatorRel;

import constraints.Constraint;
import constraints.ConstraintGlobal;
import constraints.global.AllDifferent.AllDifferentComplete;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagNotAC;
import optimization.Optimizable;
import problem.Problem;
import sets.SetDense;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * The constraint NValues imposes that the number of different values assigned to a specified list of variables respects a numerical condition.
 * 
 * @author Christophe Lecoutre
 */
public abstract class NValues extends ConstraintGlobal implements TagNotAC { // not call filtering-complete

	/**
	 * The list of variables in which we count the number of different (assigned) values
	 */
	protected final Variable[] list;

	/**
	 * Used to collect assigned values, at the beginning of the filtering process
	 */
	protected final Set<Integer> fixedVals;

	/**
	 * Used to collect relevant unassigned variables, at the beginning of the filtering process. For any variable in this set, the domain of x is not a subset
	 * of fixedVals. However, this set is computed as an approximation (for complexity reasons).
	 */
	protected final SetDense relevantUnfixedVars;

	/**
	 * sentinels[x] is a value in the domain of x that is not, at a certain moment, in fixedVals, which may explain why x is in relevantUnfixedVars
	 */
	protected final int[] sentinels;

	/**
	 * Builds a constraint NValues for the specified problem, and with the specified scope and list where to count
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 * @param list
	 *            the list of variables in which we count the number of different values
	 */
	public NValues(Problem pb, Variable[] scp, Variable[] list) {
		super(pb, scp);
		this.list = list;
		this.fixedVals = new HashSet<>(Variable.setOfvaluesIn(list).size());
		this.relevantUnfixedVars = new SetDense(list.length);
		this.sentinels = new int[list.length];
	}

	/**
	 * At the beginning of the filtering process, initialize the two sets fixedVals and relevantUnfixedVars
	 */
	protected void initializeSets() {
		fixedVals.clear();
		relevantUnfixedVars.clear();
		for (int i = 0; i < list.length; i++)
			if (list[i].dom.size() == 1)
				fixedVals.add(list[i].dom.firstValue());
			else
				relevantUnfixedVars.add(i);
		extern: for (int i = relevantUnfixedVars.limit; i >= 0; i--) {
			int x = relevantUnfixedVars.dense[i];
			Domain dom = list[x].dom;
			if (dom.size() > fixedVals.size())
				continue;
			int sentinel = sentinels[x];
			if (dom.containsValue(sentinel) && !fixedVals.contains(sentinel))
				continue;
			if (dom.size() > 5) // TODO hard coding for avoiding iterating systematically over all values
				continue;
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int v = dom.toVal(a);
				if (!fixedVals.contains(v)) {
					sentinels[x] = v;
					continue extern;
				}
			}
			relevantUnfixedVars.removeAtPosition(i); // because all values in its domain correspond to fixed values
		}
	}

	/**********************************************************************************************
	 * NValuesCst
	 *********************************************************************************************/

	/**
	 * The constraint NValues with an integer constant used as right-hand term of the numerical condition
	 */
	public static abstract class NValuesCst extends NValues implements Optimizable {

		public static Constraint buildFrom(Problem pb, Variable[] scp, TypeConditionOperatorRel op, long limit) {
			control(Variable.areAllDistinct(scp));
			switch (op) {
			case LT:
				return limit == 2 ? new AllEqual(pb, scp) : new NValuesCstLE(pb, scp, limit - 1);
			case LE:
				return limit == 1 ? new AllEqual(pb, scp) : new NValuesCstLE(pb, scp, limit);
			case GE:
				return limit == 2 ? new NotAllEqual(pb, scp) : new NValuesCstGE(pb, scp, limit);
			case GT:
				return limit == 1 ? new NotAllEqual(pb, scp) : new NValuesCstGE(pb, scp, limit + 1);
			case EQ:
				// TODO how to avoid directly setting the algorithm for AllDifferentComplete below?
				return limit == 1 ? new AllEqual(pb, scp) : limit == scp.length ? new AllDifferentComplete(pb, scp) : new NValuesCstEQ(pb, scp, limit);
			default: // case NE:
				if (limit == 1)
					return new NotAllEqual(pb, scp);
				return null; // TODO other cases not implemented
			}
		}

		/**
		 * The limit (may be dynamic, if this object is a constraint objective)
		 */
		protected long limit;

		@Override
		public long limit() {
			return limit;
		}

		@Override
		public void setLimit(long newLimit) {
			this.limit = newLimit;
		}

		@Override
		public long minComputableObjectiveValue() {
			return 1;
		}

		@Override
		public long maxComputableObjectiveValue() {
			return list.length;
		}

		@Override
		public long minCurrentObjectiveValue() {
			throw new UnsupportedOperationException("not implemented"); // how to compute that?
		}

		@Override
		public long maxCurrentObjectiveValue() {
			throw new UnsupportedOperationException("not implemented"); // how to compute that?
		}

		@Override
		public long objectiveValue() {
			return Arrays.stream(scp).mapToInt(x -> x.dom.singleValue()).distinct().count();
		}

		public NValuesCst(Problem pb, Variable[] list, long k) {
			super(pb, list, list);
			limit(k);
			control(1 <= k && k <= list.length);
			defineKey(k);
		}

		@Override
		public int[] symmetryMatching() {
			return Variable.haveSameDomainType(scp) ? Kit.repeat(1, scp.length) : Kit.series(1, scp.length);
		}

		public final static class NValuesCstLE extends NValuesCst {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return Arrays.stream(t).distinct().count() <= limit;
			}

			public NValuesCstLE(Problem pb, Variable[] list, long k) {
				super(pb, list, Math.min(k, list.length));
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (limit == Constants.PLUS_INFINITY)
					return true;
				if (x == null || x.dom.size() == 1) {
					initializeSets();
					if (fixedVals.size() > limit)
						return x == null ? false : x.dom.fail();
					if (fixedVals.size() == limit) {
						for (int i = relevantUnfixedVars.limit; i >= 0; i--)
							if (list[relevantUnfixedVars.dense[i]].dom.removeValuesNotIn(fixedVals) == false)
								return false;
						return entailed();
					}
				}
				return true;
			}
		}

		public final static class NValuesCstGE extends NValuesCst {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return Arrays.stream(t).distinct().count() >= limit;
			}

			public NValuesCstGE(Problem pb, Variable[] list, long k) {
				super(pb, list, Math.max(k, 1));
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (limit == Constants.MINUS_INFINITY)
					return true;
				if (x == null || x.dom.size() == 1) {
					initializeSets();
					if (fixedVals.size() + relevantUnfixedVars.size() < limit)
						return x == null ? false : x.dom.fail();
					if (fixedVals.size() + relevantUnfixedVars.size() == limit) {
						for (int i = relevantUnfixedVars.limit; i >= 0; i--)
							if (list[relevantUnfixedVars.dense[i]].dom.removeValuesIn(fixedVals) == false)
								return false;
						if (relevantUnfixedVars.size() == 0)
							return entailed();
					}
				}
				return true;
			}
		}

		public final static class NValuesCstEQ extends NValuesCst implements ObserverOnBacktracksSystematic {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return Arrays.stream(t).distinct().count() == limit;
			}

			@Override
			public void afterProblemConstruction(int n) {
				super.afterProblemConstruction(n);
				distinctIdxs = new SetSparseReversible(scp[0].dom.initSize(), n + 1, false);
				// it is possible to use scp[0].dom.initSize() because variables have the same domain type
			}

			@Override
			public void restoreBefore(int depth) {
				distinctIdxs.restoreLimitAtLevel(depth);
			}

			private SetSparseReversible distinctIdxs;

			private int[] residues;

			public NValuesCstEQ(Problem pb, Variable[] list, long k) {
				super(pb, list, k);
				control(Variable.haveSameDomainType(list)); // for the moment
				control(1 < k && k < list.length);
				this.residues = new int[list.length];
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (x.dom.size() == 1) {
					int a = x.dom.single();
					if (!distinctIdxs.contains(a))
						distinctIdxs.add(a, problem.solver.depth());
					int p = distinctIdxs.size();
					if (p > limit)
						return x.dom.fail();
					if (p == limit) {
						for (int j = futvars.limit; j >= 0; j--) {
							Variable y = scp[futvars.dense[j]];
							if (y != x && y.dom.removeIndexesChecking(b -> !distinctIdxs.contains(b)) == false)
								return false;
						}
						return entailed();
					}
					int cnt = 0; // we make a rough approximation to determine if limit can be reached
					for (int j = futvars.limit; j >= 0; j--) {
						int y = futvars.dense[j];
						Domain dy = scp[y].dom;
						int b = residues[y];
						if (dy.contains(b) && !distinctIdxs.contains(b))
							cnt++;
						else {
							for (b = dy.first(); b != -1; b = dy.next(b)) {
								if (!distinctIdxs.contains(b)) {
									residues[y] = b;
									cnt++;
									break;
								}
							}
						}
						if (p + cnt >= limit)
							break;
					}
				}
				return true;
			}
		}

	}

	/**********************************************************************************************
	 * NValuesVar
	 *********************************************************************************************/

	/**
	 * The constraint NValues with an integer variable used as right-hand term of the numerical condition
	 */
	public static abstract class NValuesVar extends NValues {

		public static Constraint buildFrom(Problem pb, Variable[] scp, TypeConditionOperatorRel op, Variable k) {
			control(Variable.areAllDistinct(scp));
			switch (op) {
			case EQ:
				return new NValuesVarEQ(pb, scp, k);
			default:
				return null;
			// throw new AssertionError("not implemented");
			}
		}

		/**
		 * The integer variable used as limit
		 */
		protected Variable k;

		public NValuesVar(Problem pb, Variable[] list, Variable k) {
			super(pb, pb.vars(list, k), list);
			control(Stream.of(list).noneMatch(x -> x == k), "currently, k must not be present in the list");
			this.k = k;
		}

		public final static class NValuesVarEQ extends NValuesVar {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return IntStream.range(0, t.length - 1).map(i -> t[i]).distinct().count() == t[t.length - 1];
			}

			public NValuesVarEQ(Problem pb, Variable[] list, Variable k) {
				super(pb, list, k);
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (x == null || x.dom.size() == 1) {
					initializeSets();
					if (k.dom.removeValuesLT(fixedVals.size()) == false || k.dom.removeValuesGT(fixedVals.size() + relevantUnfixedVars.size()) == false)
						return false;
					if (k.dom.size() == 1) {
						int limit = k.dom.singleValue();
						if (fixedVals.size() == limit) {
							for (int i = relevantUnfixedVars.limit; i >= 0; i--)
								if (list[relevantUnfixedVars.dense[i]].dom.removeValuesNotIn(fixedVals) == false)
									return false;
							return entailed();
						} else if (fixedVals.size() + relevantUnfixedVars.size() == limit) {
							for (int i = relevantUnfixedVars.limit; i >= 0; i--)
								if (list[relevantUnfixedVars.dense[i]].dom.removeValuesIn(fixedVals) == false)
									return false;
						}
					}
				}
				return true;
			}
		}
	}
}
