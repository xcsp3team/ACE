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
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;

import constraints.ConstraintGlobal;
import constraints.global.Extremum.ExtremumCst.MaximumCst.MaximumCstEQ;
import constraints.global.Extremum.ExtremumCst.MaximumCst.MaximumCstGE;
import constraints.global.Extremum.ExtremumCst.MaximumCst.MaximumCstLE;
import constraints.global.Extremum.ExtremumCst.MinimumCst.MinimumCstEQ;
import constraints.global.Extremum.ExtremumCst.MinimumCst.MinimumCstGE;
import constraints.global.Extremum.ExtremumCst.MinimumCst.MinimumCstLE;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagSymmetric;
import optimization.Optimizable;
import problem.Problem;
import variables.Domain;
import variables.Variable;

public abstract class Extremum extends ConstraintGlobal implements TagCallCompleteFiltering, TagAC {

	protected final Variable[] list;

	public Extremum(Problem pb, Variable[] list, Variable ext) {
		super(pb, pb.api.vars(ext, list));
		this.list = list;
	}

	public Extremum(Problem pb, Variable[] list) {
		this(pb, list, null);
	}

	public abstract static class ExtremumVar extends Extremum {

		protected final Domain domExt;

		/**
		 * sentinels[a] denotes the sentinel for the value at index a in the domain of the extremum variable
		 */
		protected final Variable[] sentinels;

		protected Variable findSentinelFor(int v, Variable except) {
			for (Variable x : list)
				if (x != except && x.dom.containsValue(v))
					return x;
			return null;
		}

		protected Variable findSentinelFor(int v) {
			for (Variable x : list)
				if (x.dom.containsValue(v))
					return x;
			return null;
		}

		@Override
		public int[] symmetryMatching() {
			return IntStream.range(0, scp.length).map(i -> i == 0 ? 1 : 2).toArray();
		}

		public ExtremumVar(Problem pb, Variable[] list, Variable ext) {
			super(pb, list, ext);
			this.domExt = ext.dom;
			this.sentinels = IntStream.range(0, domExt.initSize()).mapToObj(a -> findSentinelFor(domExt.toVal(a))).toArray(Variable[]::new);
			domExt.removeAtConstructionTime(a -> sentinels[a] == null);
			control(list.length > 1 && Stream.of(list).noneMatch(x -> x == ext), "vector length = " + list.length);
		}

		// ************************************************************************
		// ***** Constraint maximum
		// ************************************************************************

		public static final class Maximum extends ExtremumVar {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] == IntStream.range(1, t.length).map(i -> t[i]).max().getAsInt();
			}

			private int computeLimitForSentinel(Variable sentinel) {
				for (int a = domExt.last(); a != -1; a = domExt.prev(a)) {
					int v = domExt.toVal(a);
					if (sentinels[a] != sentinel || findSentinelFor(v, sentinel) != null)
						return v;
				}
				return Integer.MIN_VALUE;
			}

			public Maximum(Problem pb, Variable[] list, Variable max) {
				super(pb, list, max);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				int maxFirst = Integer.MIN_VALUE, maxLast = Integer.MIN_VALUE;
				for (Variable x : list) {
					if (x.dom.firstValue() > maxFirst)
						maxFirst = x.dom.firstValue();
					if (x.dom.lastValue() > maxLast)
						maxLast = x.dom.lastValue();
				}
				// Filtering the domain of the extremum (max) variable
				if (domExt.removeValuesLT(maxFirst) == false || domExt.removeValuesGT(maxLast) == false)
					return false;
				int sizeBefore = domExt.size();

				if (domExt.removeIndexesChecking(a -> {
					int v = domExt.toVal(a);
					if (!sentinels[a].dom.containsValue(v)) {
						Variable s = findSentinelFor(v);
						if (s == null)
							return true;
						sentinels[a] = s;
					}
					return false;
				}) == false)
					return false;

				// Filtering the domains of variables in the vector
				int lastMax = domExt.lastValue();
				for (Variable x : list)
					if (x.dom.removeValuesGT(lastMax) == false)
						return false;

				// Possibly filtering the domain of the sentinel from the last value of the Max variable
				Variable sentinel = sentinels[domExt.last()];
				int valLimit = computeLimitForSentinel(sentinel);
				if (valLimit == lastMax)
					return true; // because another sentinel exists
				Domain domSentinel = sentinel.dom;
				sizeBefore = domSentinel.size();
				for (int a = domSentinel.prev(domSentinel.last()); a != -1; a = domSentinel.prev(a)) {
					int v = domSentinel.toVal(a);
					if (v <= valLimit)
						break;
					if (!domExt.containsValue(v))
						domSentinel.removeElementary(a);
				}
				return domSentinel.afterElementaryCalls(sizeBefore); // necessarily true
			}
		}

		// ************************************************************************
		// ***** Constraint minimum
		// ************************************************************************

		public static final class Minimum extends ExtremumVar {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] == IntStream.range(1, t.length).map(i -> t[i]).min().getAsInt();
			}

			private int computeLimitForSentinel(Variable sentinel) {
				for (int a = domExt.first(); a != -1; a = domExt.next(a)) {
					int v = domExt.toVal(a);
					if (sentinels[a] != sentinel || findSentinelFor(v, sentinel) != null)
						return v;
				}
				return Integer.MAX_VALUE;
			}

			public Minimum(Problem pb, Variable[] list, Variable min) {
				super(pb, list, min);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				int minFirst = Integer.MAX_VALUE, minLast = Integer.MAX_VALUE;
				for (Variable x : list) {
					if (x.dom.firstValue() < minFirst)
						minFirst = x.dom.firstValue();
					if (x.dom.lastValue() < minLast)
						minLast = x.dom.lastValue();
				}

				// filtering the domain of the Min variable
				if (domExt.removeValuesGT(minLast) == false || domExt.removeValuesLT(minFirst) == false)
					return false;
				int sizeBefore = domExt.size();
				for (int a = domExt.first(); a != -1; a = domExt.next(a)) {
					int v = domExt.toVal(a);
					if (!sentinels[a].dom.containsValue(v)) {
						Variable s = findSentinelFor(v);
						if (s != null)
							sentinels[a] = s;
						else if (domExt.size() == 1)
							return domExt.fail();
						else
							domExt.removeElementary(a);
					}
				}
				if (domExt.afterElementaryCalls(sizeBefore) == false)
					return false;

				// Filtering the domains of variables in the vector
				int firstMin = domExt.firstValue();
				for (Variable x : list)
					if (x.dom.removeValuesLT(firstMin) == false)
						return false;

				// Possibly filtering the domain of the sentinel for the first value of the Min variable
				Variable sentinel = sentinels[domExt.first()];
				int valLimit = computeLimitForSentinel(sentinel);
				if (valLimit == firstMin)
					return true; // because another sentinel exists
				Domain domSentinel = sentinel.dom;
				sizeBefore = domSentinel.size();
				for (int a = domSentinel.next(domSentinel.first()); a != -1; a = domSentinel.next(a)) {
					int v = domSentinel.toVal(a);
					if (v >= valLimit)
						break;
					if (!domExt.containsValue(v))
						domSentinel.removeElementary(a);
				}
				return domSentinel.afterElementaryCalls(sizeBefore); // necessarily true
			}
		}
	}

	public static abstract class ExtremumCst extends Extremum implements Optimizable, TagSymmetric {

		public static ExtremumCst buildFrom(Problem pb, Variable[] list, TypeConditionOperatorRel op, long limit, boolean minimum) {
			switch (op) {
			case LT:
				return minimum ? new MinimumCstLE(pb, list, limit - 1) : new MaximumCstLE(pb, list, limit - 1);
			case LE:
				return minimum ? new MinimumCstLE(pb, list, limit) : new MaximumCstLE(pb, list, limit);
			case GE:
				return minimum ? new MinimumCstGE(pb, list, limit) : new MaximumCstGE(pb, list, limit);
			case GT:
				return minimum ? new MinimumCstGE(pb, list, limit + 1) : new MaximumCstGE(pb, list, limit + 1);
			case EQ:
				return minimum ? new MinimumCstEQ(pb, list, limit) : new MaximumCstEQ(pb, list, limit);
			default:
				throw new AssertionError("NE is not implemented"); // TODO useful to have a propagator?
			}
		}

		protected long limit;

		@Override
		public long limit() {
			return limit;
		}

		@Override
		public final void limit(long newLimit) {
			this.limit = newLimit;
			control(minComputableObjectiveValue() - 1 <= limit && limit <= maxComputableObjectiveValue() + 1);
		}

		public ExtremumCst(Problem pb, Variable[] list, long limit) {
			super(pb, list);
			limit(limit);
		}

		public static abstract class MaximumCst extends ExtremumCst {

			static long maxFirstInitialValues(Variable[] scp) {
				long max = Long.MIN_VALUE;
				for (Variable x : scp)
					max = Math.max(max, x.dom.smallestInitialValue());
				return max;
			}

			static long maxLastInitialValues(Variable[] scp) {
				long max = Long.MIN_VALUE;
				for (Variable x : scp)
					max = Math.max(max, x.dom.greatestInitialValue());
				return max;
			}

			@Override
			public long minComputableObjectiveValue() { // max of first initial values
				return maxFirstInitialValues(scp);
			}

			@Override
			public long maxComputableObjectiveValue() { // max of last initial values (global max)
				return maxLastInitialValues(scp);
			}

			@Override
			public long minCurrentObjectiveValue() { // max of first current values
				long max = Long.MIN_VALUE;
				for (Variable x : scp)
					max = Math.max(max, x.dom.firstValue());
				return max;
			}

			@Override
			public long maxCurrentObjectiveValue() { // max of last current values (global max)
				long max = Long.MIN_VALUE;
				for (Variable x : scp)
					max = Math.max(max, x.dom.lastValue());
				return max;
			}

			@Override
			public long objectiveValue() {
				return Stream.of(doms).mapToInt(dom -> dom.singleValue()).max().getAsInt();
			}

			public MaximumCst(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
			}

			public static final class MaximumCstLE extends MaximumCst {

				@Override
				public boolean isSatisfiedBy(int[] vals) {
					return IntStream.of(vals).max().getAsInt() <= limit;
				}

				public MaximumCstLE(Problem pb, Variable[] scp, long limit) {
					super(pb, scp, Math.min(limit, maxLastInitialValues(scp)));
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					control(problem.solver.depth() == 0);
					for (Variable y : scp)
						if (y.dom.removeValuesGT(limit) == false)
							return false;
					return entailed();
				}
			}

			public static final class MaximumCstGE extends MaximumCst {

				@Override
				public boolean isSatisfiedBy(int[] vals) {
					return IntStream.of(vals).max().getAsInt() >= limit;
				}

				private int sentinel1, sentinel2;

				public MaximumCstGE(Problem pb, Variable[] scp, long limit) {
					super(pb, scp, Math.max(limit, maxFirstInitialValues(scp)));
					this.sentinel1 = 0;
					this.sentinel2 = scp.length - 1;
					control(scp[sentinel1].dom.lastValue() >= limit && scp[sentinel2].dom.lastValue() >= limit, "unsound sentinels");
				}

				@Override
				public boolean runPropagator(Variable x) {
					if (scp[sentinel1].dom.lastValue() < limit) {
						int i = 0;
						for (; i < scp.length; i++)
							if (i != sentinel2 && scp[i].dom.lastValue() >= limit)
								break;
						if (i < scp.length)
							sentinel1 = i;
						else {
							if (scp[sentinel2].dom.lastValue() < limit)
								return x == null ? false : x.dom.fail();
							scp[sentinel2].dom.removeValuesLT(limit);
							return entailed();
						}
					}
					if (scp[sentinel2].dom.lastValue() < limit) {
						int i = 0;
						for (; i < scp.length; i++)
							if (i != sentinel1 && scp[i].dom.lastValue() >= limit)
								break;
						if (i < scp.length)
							sentinel2 = i;
						else {
							assert scp[sentinel1].dom.lastValue() >= limit;
							scp[sentinel1].dom.removeValuesLT(limit);
							return entailed();

						}
					}
					return true;
				}
			}

			public static final class MaximumCstEQ extends MaximumCst {
				// the code is similar to Atleast1 (modulo initial filtering, and call-filtering complete)
				// TODO: only one class for MaximumCstEQ, MinimumCstEQ and Atleast1 ?

				@Override
				public boolean isSatisfiedBy(int[] vals) {
					return IntStream.of(vals).max().getAsInt() == limit;
				}

				private int value;

				/** Two sentinels for tracking the presence of the value. */
				private Variable sentinel1, sentinel2;

				public MaximumCstEQ(Problem pb, Variable[] scp, long limit) {
					super(pb, scp, limit);
					this.value = Utilities.safeInt(limit, true);
					for (Variable x : scp)
						x.dom.removeValuesAtConstructionTime(v -> v > this.value); // making it more efficient?
					this.sentinel1 = scp[0];
					this.sentinel2 = scp[1];
				}

				private Variable findAnotherSentinel() {
					for (Variable x : scp)
						if (x != sentinel1 && x != sentinel2 && x.dom.containsValue(value))
							return x;
					return null;
				}

				@Override
				public boolean runPropagator(Variable x) {
					if (!sentinel1.dom.containsValue(value)) {
						Variable sentinel = findAnotherSentinel();
						if (sentinel != null)
							sentinel1 = sentinel;
						else
							return sentinel2.dom.reduceToValue(value) && entailed();
					}
					if (!sentinel2.dom.containsValue(value)) {
						Variable sentinel = findAnotherSentinel();
						if (sentinel != null)
							sentinel2 = sentinel;
						else
							return sentinel1.dom.reduceToValue(value) && entailed();
					}
					return true;
				}
			}
		}

		public static abstract class MinimumCst extends ExtremumCst {

			static long minFirstInitialValues(Variable[] scp) {
				long min = Long.MAX_VALUE;
				for (Variable x : scp)
					min = Math.min(min, x.dom.smallestInitialValue());
				return min;
			}

			static long minLastInitialValues(Variable[] scp) {
				long min = Long.MAX_VALUE;
				for (Variable x : scp)
					min = Math.min(min, x.dom.greatestInitialValue());
				return min;
			}

			@Override
			public long minComputableObjectiveValue() { // min of first initial values (global min)
				return minFirstInitialValues(scp);
			}

			@Override
			public long maxComputableObjectiveValue() { // min of last initial values
				return minLastInitialValues(scp);
			}

			@Override
			public long minCurrentObjectiveValue() { // min of first current values (global min)
				long min = Long.MAX_VALUE;
				for (Variable x : scp)
					min = Math.min(min, x.dom.firstValue());
				return min;
			}

			@Override
			public long maxCurrentObjectiveValue() { // min of last current values
				long min = Long.MAX_VALUE;
				for (Variable x : scp)
					min = Math.min(min, x.dom.lastValue());
				return min;
			}

			@Override
			public long objectiveValue() {
				return Stream.of(doms).mapToInt(dom -> dom.singleValue()).min().getAsInt();
			}

			public MinimumCst(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
			}

			public static final class MinimumCstLE extends MinimumCst {

				@Override
				public boolean isSatisfiedBy(int[] vals) {
					return IntStream.of(vals).min().getAsInt() <= limit;
				}

				private int sentinel1, sentinel2;

				public MinimumCstLE(Problem pb, Variable[] scp, long limit) {
					super(pb, scp, Math.min(limit, minLastInitialValues(scp)));
					sentinel1 = 0;
					sentinel2 = scp.length - 1;
					control(scp[sentinel1].dom.firstValue() <= limit && scp[sentinel2].dom.firstValue() <= limit, "unsound sentinels");
				}

				@Override
				public boolean runPropagator(Variable x) {
					if (scp[sentinel1].dom.firstValue() > limit) {
						int i = 0;
						for (; i < scp.length; i++)
							if (i != sentinel2 && scp[i].dom.firstValue() <= limit)
								break;
						if (i < scp.length)
							sentinel1 = i;
						else {
							if (scp[sentinel2].dom.firstValue() > limit)
								return x == null ? false : x.dom.fail();
							scp[sentinel2].dom.removeValuesGT(limit);
							return entailed();
						}
					}
					if (scp[sentinel2].dom.firstValue() > limit) {
						int i = 0;
						for (; i < scp.length; i++)
							if (i != sentinel1 && scp[i].dom.firstValue() <= limit)
								break;
						if (i < scp.length)
							sentinel2 = i;
						else {
							assert scp[sentinel1].dom.firstValue() <= limit;
							scp[sentinel1].dom.removeValuesGT(limit);
							return entailed();
						}
					}
					return true;
				}
			}

			public static final class MinimumCstGE extends MinimumCst {

				@Override
				public boolean isSatisfiedBy(int[] vals) {
					return IntStream.of(vals).min().getAsInt() >= limit;
				}

				public MinimumCstGE(Problem pb, Variable[] scp, long limit) {
					super(pb, scp, Math.max(limit, minFirstInitialValues(scp)));
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					control(problem.solver.depth() == 0);
					for (Variable y : scp)
						if (y.dom.removeValuesLT(limit) == false)
							return false;
					return entailed();
				}
			}

			public static final class MinimumCstEQ extends MinimumCst {
				// the code is similar to Atleast1 (modulo initial filtering, and call-filtering complete)

				@Override
				public boolean isSatisfiedBy(int[] vals) {
					return IntStream.of(vals).min().getAsInt() == limit;
				}

				private int value;

				/** Two sentinels for tracking the presence of the value. */
				private Variable sentinel1, sentinel2;

				public MinimumCstEQ(Problem pb, Variable[] scp, long limit) {
					super(pb, scp, limit);
					this.value = Utilities.safeInt(limit, true);
					for (Variable x : scp)
						x.dom.removeValuesAtConstructionTime(v -> v < this.value); // making it more efficient?
					this.sentinel1 = scp[0];
					this.sentinel2 = scp[1];
				}

				private Variable findAnotherSentinel() {
					for (Variable x : scp)
						if (x != sentinel1 && x != sentinel2 && x.dom.containsValue(value))
							return x;
					return null;
				}

				@Override
				public boolean runPropagator(Variable x) {
					if (!sentinel1.dom.containsValue(value)) {
						Variable sentinel = findAnotherSentinel();
						if (sentinel != null)
							sentinel1 = sentinel;
						else
							return sentinel2.dom.reduceToValue(value) && entailed();
					}
					if (!sentinel2.dom.containsValue(value)) {
						Variable sentinel = findAnotherSentinel();
						if (sentinel != null)
							sentinel2 = sentinel;
						else
							return sentinel1.dom.reduceToValue(value) && entailed();
					}
					return true;
				}
			}

		}

	}
}
