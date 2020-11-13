package constraints.global;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint.CtrGlobal;
import interfaces.Optimizable;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagSymmetric;
import problem.Problem;
import variables.Variable;
import variables.domains.Domain;

public abstract class Extremum extends CtrGlobal implements TagFilteringCompleteAtEachCall, TagGACGuaranteed {

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
				if (x != except && x.dom.isPresentValue(v))
					return x;
			return null;
		}

		protected Variable findSentinelFor(int v) {
			for (Variable x : list)
				if (x.dom.isPresentValue(v))
					return x;
			return null;
		}

		@Override
		public int[] defineSymmetryMatching() {
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
			public boolean checkValues(int[] t) {
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
					if (!sentinels[a].dom.isPresentValue(v)) {
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
					if (!domExt.isPresentValue(v))
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
			public boolean checkValues(int[] t) {
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
					if (!sentinels[a].dom.isPresentValue(v)) {
						Variable s = findSentinelFor(v);
						if (s != null)
							sentinels[a] = s;
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
					if (!domExt.isPresentValue(v))
						domSentinel.removeElementary(a);
				}
				return domSentinel.afterElementaryCalls(sizeBefore); // necessarily true
			}
		}
	}

	public static abstract class ExtremumCst extends Extremum implements Optimizable, TagSymmetric {

		protected int limit;

		protected boolean entailed;

		@Override
		public long minComputableObjectiveValue() {
			return Stream.of(scp).mapToLong(x -> x.dom.toVal(0)).min().getAsLong(); // stream not a problem as only called once at construction time
		}

		@Override
		public long maxComputableObjectiveValue() {
			return Stream.of(scp).mapToLong(x -> x.dom.toVal(x.dom.initSize() - 1)).max().getAsLong(); // not a problem as only called once
		}

		@Override
		public long getLimit() {
			return limit;
		}

		@Override
		public final void setLimit(long newLimit) {
			this.limit = Math.toIntExact(newLimit);
			entailed = false;
		}

		public ExtremumCst(Problem pb, Variable[] list, int limit) {
			super(pb, list);
			this.limit = limit;
		}

		public static abstract class MaximumCst extends ExtremumCst {

			@Override
			public long objectiveValue() {
				return Stream.of(doms).mapToInt(dom -> dom.uniqueValue()).max().getAsInt();
			}

			public MaximumCst(Problem pb, Variable[] scp, int limit) {
				super(pb, scp, limit);
			}

			public static final class MaximumCstLE extends MaximumCst {

				@Override
				public boolean checkValues(int[] vals) {
					return IntStream.of(vals).max().getAsInt() <= limit;
				}

				public MaximumCstLE(Problem pb, Variable[] scp, int limit) {
					super(pb, scp, limit);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (entailed)
						return true;
					control(pb.solver.depth() == 0);
					for (Variable y : scp)
						if (y.dom.removeValuesGT(limit) == false) {
							return false;
						}
					entailed = true;
					return Variable.firstWipeoutVariableIn(scp) == null;
				}
			}

			public static final class MaximumCstGE extends MaximumCst {

				@Override
				public boolean checkValues(int[] vals) {
					return IntStream.of(vals).max().getAsInt() >= limit;
				}

				private int sentinel1, sentinel2;

				public MaximumCstGE(Problem pb, Variable[] scp, int limit) {
					super(pb, scp, limit);
					sentinel1 = 0;
					sentinel2 = scp.length - 1;
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
							else
								return scp[sentinel2].dom.removeValuesLT(limit); // necessarily true returned
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
							return scp[sentinel2].dom.removeValuesLT(limit); // necessarily true returned
						}
					}
					return true;
					// TODO manage entailed below ?
				}
			}

		}

		public static abstract class MinimumCst extends ExtremumCst {

			@Override
			public long objectiveValue() {
				return Stream.of(doms).mapToInt(dom -> dom.uniqueValue()).min().getAsInt();
			}

			public MinimumCst(Problem pb, Variable[] scp, int limit) {
				super(pb, scp, limit);
			}

			public static final class MinimumCstLE extends MinimumCst {

				@Override
				public boolean checkValues(int[] vals) {
					return IntStream.of(vals).min().getAsInt() <= limit;
				}

				private int sentinel1, sentinel2;

				public MinimumCstLE(Problem pb, Variable[] scp, int limit) {
					super(pb, scp, limit);
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
							else
								return scp[sentinel2].dom.removeValuesGT(limit); // necessarily true returned
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
							return scp[sentinel2].dom.removeValuesGT(limit); // necessarily true returned
						}
					}
					return true;
				}
			}

			public static final class MinimumCstGE extends MinimumCst {

				@Override
				public boolean checkValues(int[] vals) {
					return IntStream.of(vals).min().getAsInt() >= limit;
				}

				public MinimumCstGE(Problem pb, Variable[] scp, int limit) {
					super(pb, scp, limit);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (entailed)
						return true;
					control(pb.solver.depth() == 0);
					for (Variable y : scp)
						if (y.dom.removeValuesLT(limit) == false)
							return false;
					entailed = true;
					return Variable.firstWipeoutVariableIn(scp) == null;
				}
			}

		}

	}
}
