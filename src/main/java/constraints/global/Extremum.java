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

import static utility.Kit.control;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
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
import interfaces.Tags.TagBoundCompatible;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagSymmetric;
import optimization.Optimizable;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * The constraints Minimum and Maximum ensure that the minimal values or maximal values assigned to the variables in the scope of the constraint respects a
 * condition. This is the abstract root class.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Extremum extends ConstraintGlobal implements TagAC, TagCallCompleteFiltering {

	/**
	 * The list (vector) of variables
	 */
	protected final Variable[] list;

	public Extremum(Problem pb, Variable[] list, Variable ext) {
		super(pb, pb.api.vars(ext, list)); // ext may be null
		this.list = list;
	}

	/**********************************************************************************************
	 * ExtremumVar, with its two subclasses Maximum and Minimum
	 *********************************************************************************************/

	public abstract static class ExtremumVar extends Extremum implements TagBoundCompatible {

		/**
		 * The domain of the target variable (used as value)
		 */
		protected final Domain vdom;

		/**
		 * sentinels[a] denotes the sentinel for the value at index a in the domain of the extremum variable
		 */
		protected final Variable[] sentinels;

		public ExtremumVar(Problem pb, Variable[] list, Variable value) {
			super(pb, list, value);
			this.vdom = value.dom;
			this.sentinels = specialServants == null
					? IntStream.range(0, vdom.initSize()).mapToObj(a -> findSentinelFor(vdom.toVal(a))).toArray(Variable[]::new)
					: null; // otherwise may be too long (since large domains)
			if (sentinels != null)
				vdom.removeAtConstructionTime(a -> sentinels[a] == null);
			control(list.length > 1 && Stream.of(list).noneMatch(x -> x == value), "vector length = " + list.length);
		}

		@Override
		public int[] symmetryMatching() {
			return IntStream.range(0, scp.length).map(i -> i == 0 ? 1 : 2).toArray();
		}

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

		// ************************************************************************
		// ***** Constraint Maximum
		// ************************************************************************

		public static final class Maximum extends ExtremumVar {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				boolean found = false;
				for (int i = 1; i < t.length; i++) {
					if (t[i] > t[0])
						return false;
					if (t[i] == t[0])
						found = true;
				}
				return found;
			}

			public Maximum(Problem pb, Variable[] list, Variable value) {
				super(pb, list, value);
			}

			private int computeLimitForSentinel(Variable sentinel) {
				for (int a = vdom.last(); a != -1; a = vdom.prev(a)) {
					int v = vdom.toVal(a);
					if (sentinels[a] != sentinel || findSentinelFor(v, sentinel) != null)
						return v;
				}
				return Integer.MIN_VALUE;
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
				// Filtering vdom (the domain of the target extremum variable)
				if (vdom.removeValuesLT(maxFirst) == false || vdom.removeValuesGT(maxLast) == false)
					return false;

				int sizeBefore = vdom.size();

				if (sentinels != null)
					if (vdom.removeIndexesChecking(a -> {
						int v = vdom.toVal(a);
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
				int lastMax = vdom.lastValue();
				for (Variable x : list)
					if (x.dom.removeValuesGT(lastMax) == false)
						return false;

				if (sentinels == null)
					return true;

				// Possibly filtering the domain of the sentinel from the last value of vdom
				Variable sentinel = sentinels[vdom.last()];
				int valLimit = computeLimitForSentinel(sentinel);
				if (valLimit == lastMax)
					return true; // because another sentinel exists
				Domain domSentinel = sentinel.dom;
				sizeBefore = domSentinel.size();
				for (int a = domSentinel.prev(domSentinel.last()); a != -1; a = domSentinel.prev(a)) {
					int v = domSentinel.toVal(a);
					if (v <= valLimit)
						break;
					if (!vdom.containsValue(v))
						domSentinel.removeElementary(a);
				}
				return domSentinel.afterElementaryCalls(sizeBefore); // necessarily true
			}
		}

		// ************************************************************************
		// ***** Constraint Minimum
		// ************************************************************************

		public static final class Minimum extends ExtremumVar {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				boolean found = false;
				for (int i = 1; i < t.length; i++) {
					if (t[i] < t[0])
						return false;
					if (t[i] == t[0])
						found = true;
				}
				return found;
			}

			public Minimum(Problem pb, Variable[] list, Variable value) {
				super(pb, list, value);
			}

			private int computeLimitForSentinel(Variable sentinel) {
				for (int a = vdom.first(); a != -1; a = vdom.next(a)) {
					int v = vdom.toVal(a);
					if (sentinels[a] != sentinel || findSentinelFor(v, sentinel) != null)
						return v;
				}
				return Integer.MAX_VALUE;
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
				// filtering the domain of vdom
				if (vdom.removeValuesGT(minLast) == false || vdom.removeValuesLT(minFirst) == false)
					return false;

				int sizeBefore = vdom.size();

				if (sentinels != null) {
					for (int a = vdom.first(); a != -1; a = vdom.next(a)) {
						int v = vdom.toVal(a);
						if (!sentinels[a].dom.containsValue(v)) {
							Variable s = findSentinelFor(v);
							if (s != null)
								sentinels[a] = s;
							else if (vdom.size() == 1)
								return vdom.fail();
							else
								vdom.removeElementary(a);
						}
					}
					if (vdom.afterElementaryCalls(sizeBefore) == false)
						return false;
				}

				// Filtering the domains of variables in the list
				int firstMin = vdom.firstValue();
				for (Variable x : list)
					if (x.dom.removeValuesLT(firstMin) == false)
						return false;

				if (sentinels == null)
					return true;

				// Possibly filtering the domain of the sentinel for the first value of vdom
				Variable sentinel = sentinels[vdom.first()];
				int valLimit = computeLimitForSentinel(sentinel);
				if (valLimit == firstMin)
					return true; // because another sentinel exists
				Domain domSentinel = sentinel.dom;
				sizeBefore = domSentinel.size();
				for (int a = domSentinel.next(domSentinel.first()); a != -1; a = domSentinel.next(a)) {
					int v = domSentinel.toVal(a);
					if (v >= valLimit)
						break;
					if (!vdom.containsValue(v))
						domSentinel.removeElementary(a);
				}
				return domSentinel.afterElementaryCalls(sizeBefore); // necessarily true
			}
		}
	}

	/**********************************************************************************************
	 * ExtremumCst, with its two subclasses MaximumCst and MinimumCst
	 *********************************************************************************************/

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
			default: // NE
				throw new AssertionError("NE is not implemented"); // TODO useful to have a propagator?
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
		public final void setLimit(long newLimit) {
			this.limit = newLimit;
		}

		public ExtremumCst(Problem pb, Variable[] list, long limit) {
			super(pb, list, null);
			limit(limit);
		}

		// ************************************************************************
		// ***** Constraints MaximumCst
		// ************************************************************************

		public static abstract class MaximumCst extends ExtremumCst {

			public static long maxFirstInitialValues(Variable[] scp) {
				long max = Long.MIN_VALUE;
				for (Variable x : scp)
					max = Math.max(max, x.dom.smallestInitialValue());
				return max;
			}

			public static long maxLastInitialValues(Variable[] scp) {
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
				long max = Long.MIN_VALUE;
				for (Variable x : scp)
					max = Math.max(max, x.dom.lastValue());
				return max;
				// return maxCurrentObjectiveValue(); // = minCurrentObjectiveValue()
			}

			public MaximumCst(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
			}

			public static final class MaximumCstLE extends MaximumCst implements TagBoundCompatible {

				@Override
				public boolean isSatisfiedBy(int[] vals) {
					for (int v : vals)
						if (v > limit)
							return false;
					return true;
				}

				public MaximumCstLE(Problem pb, Variable[] scp, long limit) {
					super(pb, scp, Math.min(limit, maxLastInitialValues(scp)));
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					// control(problem.solver.depth() == 0); // Not possible when used as objective constraint?
					if (limit == Constants.PLUS_INFINITY)
						return true;
					for (Variable y : scp)
						if (y.dom.removeValuesGT(limit) == false)
							return false;
					return entail();
				}
			}

			public static final class MaximumCstGE extends MaximumCst {

				@Override
				public boolean isSatisfiedBy(int[] vals) {
					for (int v : vals)
						if (v >= limit)
							return true;
					return false;
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
					if (limit == Constants.MINUS_INFINITY)
						return true;
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
							return entail();
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
							return entail();

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
					boolean found = false;
					for (int v : vals) {
						if (v > value)
							return false;
						if (v == value)
							found = true;
					}
					return found;
				}

				private final int value;

				/** Two sentinels for tracking the presence of the value. */
				private Variable sentinel1, sentinel2;

				public MaximumCstEQ(Problem pb, Variable[] scp, long limit) {
					super(pb, scp, limit);
					this.value = Utilities.safeInt(limit, true);
					// we remove any value strictly greater than value ; this way we can reason with two sentinels
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
				public boolean runPropagator(Variable dummy) {
					if (!sentinel1.dom.containsValue(value)) {
						Variable sentinel = findAnotherSentinel();
						if (sentinel != null)
							sentinel1 = sentinel;
						else
							return sentinel2.dom.reduceToValue(value) && entail();
					}
					if (!sentinel2.dom.containsValue(value)) {
						Variable sentinel = findAnotherSentinel();
						if (sentinel != null)
							sentinel2 = sentinel;
						else
							return sentinel1.dom.reduceToValue(value) && entail();
					}
					return true;
				}
			}
		}

		// ************************************************************************
		// ***** Constraints MinimumCst
		// ************************************************************************

		public static abstract class MinimumCst extends ExtremumCst {

			public static long minFirstInitialValues(Variable[] scp) {
				long min = Long.MAX_VALUE;
				for (Variable x : scp)
					min = Math.min(min, x.dom.smallestInitialValue());
				return min;
			}

			public static long minLastInitialValues(Variable[] scp) {
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
				long min = Long.MAX_VALUE;
				for (Variable x : scp)
					min = Math.min(min, x.dom.firstValue());
				return min;
				// return minCurrentObjectiveValue(); // = maxCurrentObjectiveValue
			}

			public MinimumCst(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
			}

			public static final class MinimumCstLE extends MinimumCst {

				@Override
				public boolean isSatisfiedBy(int[] vals) {
					for (int v : vals)
						if (v <= limit)
							return true;
					return false;
				}

				private int sentinel1, sentinel2;

				public MinimumCstLE(Problem pb, Variable[] scp, long limit) {
					super(pb, scp, Math.min(limit, minLastInitialValues(scp)));
					this.sentinel1 = 0;
					this.sentinel2 = scp.length - 1;
					control(scp[sentinel1].dom.firstValue() <= limit && scp[sentinel2].dom.firstValue() <= limit, "unsound sentinels");
				}

				@Override
				public boolean runPropagator(Variable x) {
					if (limit == Constants.PLUS_INFINITY)
						return true;
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
							return entail();
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
							return entail();
						}
					}
					return true;
				}
			}

			public static final class MinimumCstGE extends MinimumCst implements TagBoundCompatible {

				@Override
				public boolean isSatisfiedBy(int[] vals) {
					for (int v : vals)
						if (v < limit)
							return false;
					return true;
				}

				public MinimumCstGE(Problem pb, Variable[] scp, long limit) {
					super(pb, scp, Math.max(limit, minFirstInitialValues(scp)));
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					// control(problem.solver.depth() == 0);
					if (limit == Constants.MINUS_INFINITY)
						return true;
					for (Variable y : scp)
						if (y.dom.removeValuesLT(limit) == false)
							return false;
					return entail();
				}
			}

			public static final class MinimumCstEQ extends MinimumCst {
				// the code is similar to Atleast1 (modulo initial filtering, and call-filtering complete)

				@Override
				public boolean isSatisfiedBy(int[] vals) {
					boolean found = false;
					for (int v : vals) {
						if (v < value)
							return false;
						if (v == value)
							found = true;
					}
					return found;
				}

				private final int value;

				/** Two sentinels for tracking the presence of the value. */
				private Variable sentinel1, sentinel2;

				public MinimumCstEQ(Problem pb, Variable[] scp, long limit) {
					super(pb, scp, limit);
					this.value = Utilities.safeInt(limit, true);
					// we remove any value strictly less than value ; this way we can reason with two sentinels
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
				public boolean runPropagator(Variable dummy) {
					if (!sentinel1.dom.containsValue(value)) {
						Variable sentinel = findAnotherSentinel();
						if (sentinel != null)
							sentinel1 = sentinel;
						else
							return sentinel2.dom.reduceToValue(value) && entail();
					}
					if (!sentinel2.dom.containsValue(value)) {
						Variable sentinel = findAnotherSentinel();
						if (sentinel != null)
							sentinel2 = sentinel;
						else
							return sentinel1.dom.reduceToValue(value) && entail();
					}
					return true;
				}
			}

		}

	}
}
