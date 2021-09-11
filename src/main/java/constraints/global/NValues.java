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

import org.xcsp.common.Types.TypeConditionOperatorRel;

import constraints.Constraint;
import constraints.ConstraintGlobal;
import constraints.global.AllDifferent.AllDifferentComplete;
import interfaces.Tags.TagNotAC;
import optimization.Optimizable;
import problem.Problem;
import sets.SetDense;
import variables.Domain;
import variables.Variable;

public abstract class NValues extends ConstraintGlobal implements TagNotAC { // not call filtering-complete

	/**
	 * the array of variables in which we count the number of different (assigned) values
	 */
	protected final Variable[] list;

	protected final Set<Integer> fixedVals;

	protected final SetDense unfixedVars; // unfixed variables with domains not in fixed vals (this is an approximation)

	protected final int[] sentinels;

	public NValues(Problem pb, Variable[] scp, Variable[] list) {
		super(pb, scp);
		this.list = list;
		this.fixedVals = new HashSet<>(Variable.setOfvaluesIn(list).size());
		this.unfixedVars = new SetDense(list.length);
		this.sentinels = new int[list.length];
	}

	protected void initializeSets() {
		fixedVals.clear();
		unfixedVars.clear();
		for (int i = 0; i < list.length; i++)
			if (list[i].dom.size() == 1)
				fixedVals.add(list[i].dom.firstValue());
			else
				unfixedVars.add(i);
		extern: for (int i = unfixedVars.limit; i >= 0; i--) {
			int x = unfixedVars.dense[i];
			Domain dom = list[x].dom;
			if (dom.size() > fixedVals.size())
				continue;
			int sentinel = sentinels[x];
			if (dom.containsValue(sentinel) && !fixedVals.contains(sentinel))
				continue;
			if (dom.size() > 5) // hard coding for avoiding iterating systematically over all values
				continue;
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int va = dom.toVal(a);
				if (!fixedVals.contains(va)) {
					sentinels[x] = va;
					continue extern;
				}
			}
			unfixedVars.removeAtPosition(i); // because all values in its domain correspond to fixed values
		}
	}

	/**********************************************************************************************
	 * NValuesCst
	 *********************************************************************************************/

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
				if (limit == 1)
					return new AllEqual(pb, scp);
				if (limit == scp.length)
					return new AllDifferentComplete(pb, scp);
				return null; // TODO other cases not implemented
			default: // case NE:
				if (limit == 1)
					return new NotAllEqual(pb, scp);
				return null; // TODO other cases not implemented
			}
		}

		protected long limit;

		@Override
		public long limit() {
			return limit;
		}

		@Override
		public void limit(long newLimit) {
			this.limit = newLimit;
			control(minComputableObjectiveValue() <= limit && limit <= maxComputableObjectiveValue());
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
			defineKey(k);
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
				if (x == null || x.dom.size() == 1) {
					initializeSets();
					if (fixedVals.size() > limit)
						return x == null ? false : x.dom.fail();
					if (fixedVals.size() == limit) {
						for (int i = unfixedVars.limit; i >= 0; i--)
							if (list[unfixedVars.dense[i]].dom.removeValuesNotIn(fixedVals) == false)
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
				if (x == null || x.dom.size() == 1) {
					initializeSets();
					if (fixedVals.size() + unfixedVars.size() < limit)
						return x == null ? false : x.dom.fail();
					if (fixedVals.size() + unfixedVars.size() == limit) {
						for (int i = unfixedVars.limit; i >= 0; i--)
							if (list[unfixedVars.dense[i]].dom.removeValuesIn(fixedVals) == false)
								return false;
						if (unfixedVars.size() == 0)
							return entailed();
					}
				}
				return true;
			}
		}
	}

	/**********************************************************************************************
	 * NValuesVar
	 *********************************************************************************************/

	public static abstract class NValuesVar extends NValues {

		public static Constraint buildFrom(Problem pb, Variable[] scp, TypeConditionOperatorRel op, Variable k) {
			control(Variable.areAllDistinct(scp));
			switch (op) {
			case EQ:
				return new NValuesVarEQ(pb, scp, k);
			default:
				throw new AssertionError("not implemented");
			}
		}

		protected Variable k;

		public NValuesVar(Problem pb, Variable[] list, Variable k) {
			super(pb, pb.vars(list, k), list);
			control(Stream.of(list).noneMatch(x -> x == k), "currently, k must not be present in the list");
			this.k = k;
		}

		public static final class NValuesVarEQ extends NValuesVar {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return IntStream.range(0, t.length - 1).map(i -> t[i]).distinct().count() == t[t.length - 1];
			}

			public NValuesVarEQ(Problem pb, Variable[] list, Variable k) {
				super(pb, list, k);
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (x.dom.size() == 1) {
					initializeSets();
					if (k.dom.removeValuesLT(fixedVals.size()) == false || k.dom.removeValuesGT(fixedVals.size() + unfixedVars.size()) == false)
						return false;
					if (k.dom.size() == 1) {
						int limit = k.dom.singleValue();
						if (fixedVals.size() == limit) {
							for (int i = unfixedVars.limit; i >= 0; i--)
								if (list[unfixedVars.dense[i]].dom.removeValuesNotIn(fixedVals) == false)
									return false;
							return entailed();
						} else if (fixedVals.size() + unfixedVars.size() == limit) {
							for (int i = unfixedVars.limit; i >= 0; i--)
								if (list[unfixedVars.dense[i]].dom.removeValuesIn(fixedVals) == false)
									return false;
						}
					}
				}
				return true;
			}
		}
	}
}
