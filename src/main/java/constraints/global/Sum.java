/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import static org.xcsp.common.Types.TypeOperatorRel.GT;
import static org.xcsp.common.Types.TypeOperatorRel.LT;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;

import constraints.Constraint.CtrGlobal;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagSymmetric;
import optimization.Optimizable;
import problem.Problem;
import utility.Kit;
import variables.Domain;
import variables.DomainInfinite;
import variables.Variable;

public abstract class Sum extends CtrGlobal implements TagFilteringCompleteAtEachCall {

	protected long limit;

	protected long min, max; // used in most of the subclasses

	public final long limit() {
		return limit;
	}

	public void limit(long newLimit) {
		this.limit = newLimit;
	}

	public Sum(Problem pb, Variable[] scp, long limit) {
		super(pb, scp);
		limit(limit);
		control(scp.length > 1);
	}

	/**
	 * Only used in some subclasses
	 */
	protected boolean controlFCLevel() {
		int singletonPosition = -1;
		for (int i = 0; i < scp.length; i++) {
			if (scp[i].dom.size() == 1)
				vals[i] = scp[i].dom.uniqueValue();
			else if (singletonPosition == -1)
				singletonPosition = i;
			else
				return true;
		}
		if (singletonPosition == -1)
			return checkValues(vals);
		Domain dom = scp[singletonPosition].dom;
		for (int a = dom.first(); a != -1; a = dom.next(a)) {
			vals[singletonPosition] = dom.toVal(a);
			Kit.control(checkValues(vals), () -> "pb with " + Kit.join(vals));
		}
		return true;
	}

	/**********************************************************************************************
	 * SumSimple
	 *********************************************************************************************/

	/**
	 * Root class for managing simple sum constraints (i.e., sum constraints without integer coefficients associated with variables). Note that no overflow is
	 * possible because all sum of integer values (int) cannot exceed long values.
	 */
	public static abstract class SumSimple extends Sum implements TagSymmetric {

		public static SumSimple buildFrom(Problem pb, Variable[] scp, TypeConditionOperatorRel op, long limit) {
			switch (op) {
			case LT:
				return new SumSimpleLE(pb, scp, limit - 1);
			case LE:
				return new SumSimpleLE(pb, scp, limit);
			case GE:
				return new SumSimpleGE(pb, scp, limit);
			case GT:
				return new SumSimpleGE(pb, scp, limit + 1);
			case EQ:
				return new SumSimpleEQ(pb, scp, limit);
			case NE:
				return new SumSimpleNE(pb, scp, limit);
			}
			throw new AssertionError();
		}

		public static long sum(int[] t) {
			long l = 0;
			for (int v : t)
				l += v;
			return l;
		}

		public static long minPossibleSum(Variable[] scp) {
			long sum = 0;
			for (Variable x : scp)
				sum += x.dom.toVal(0);
			return sum;
		}

		public static long maxPossibleSum(Variable[] scp) {
			long sum = 0;
			for (Variable x : scp)
				sum += x.dom.toVal(x.dom.initSize() - 1);
			return sum;
		}

		public final long minComputableObjectiveValue() {
			return minPossibleSum(scp);
		}

		public final long maxComputableObjectiveValue() {
			return maxPossibleSum(scp);
		}

		public final long minCurrentObjectiveValue() {
			long sum = 0;
			for (Variable x : scp)
				sum += x.dom.firstValue();
			return sum;
		}

		public final long maxCurrentObjectiveValue() {
			long sum = 0;
			for (Variable x : scp)
				sum += x.dom.lastValue();
			return sum;
		}

		protected final long currSum() {
			long sum = 0;
			for (Variable x : scp)
				sum += x.dom.uniqueValue();
			return sum;
		}

		public final void limit(long newLimit) {
			super.limit(newLimit);
			control(minComputableObjectiveValue() - 1 <= limit && limit <= maxComputableObjectiveValue() + 1,
					"min:" + minComputableObjectiveValue() + " max:" + maxComputableObjectiveValue() + " limit:" + limit);
		}

		public SumSimple(Problem pb, Variable[] scp, long limit) {
			super(pb, scp, limit);
			defineKey(limit);
		}

		protected final void recomputeBounds() {
			min = max = 0;
			for (Variable x : scp) {
				min += x.dom.firstValue();
				max += x.dom.lastValue();
			}
		}

		// ************************************************************************
		// ***** Constraint SumSimpleLE
		// ************************************************************************

		public static class SumSimpleLE extends SumSimple implements TagGACGuaranteed, Optimizable {

			@Override
			public final boolean checkValues(int[] t) {
				return sum(t) <= limit;
			}

			@Override
			public long objectiveValue() {
				return currSum();
			}

			public SumSimpleLE(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, Math.min(limit, maxPossibleSum(scp)));
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (max <= limit)
					return entailed();
				if (min > limit)
					return x == null ? false : x.dom.fail();
				for (int i = futvars.limit; i >= 0; i--) {
					Domain dom = scp[futvars.dense[i]].dom;
					if (dom.size() == 1)
						continue;
					max -= dom.lastValue();
					dom.removeValuesGT(limit - (min - dom.firstValue()));
					assert dom.size() > 0;
					max += dom.lastValue();
					if (max <= limit)
						return true;
				}
				return true;
			}

			public Variable mostImpacting() { // experimental
				int[] solution = problem.solver.solRecorder.lastSolution;
				List<Variable> list = new ArrayList<>();
				int bestGap = Integer.MIN_VALUE;
				for (Variable x : scp) {
					int gap = x.dom.toVal(solution[x.num]) - x.dom.firstValue();
					if (gap > bestGap) {
						list.clear();
						list.add(x);
						bestGap = gap;
					} else if (gap == bestGap)
						list.add(x);
				}
				System.out.println("bestgap " + bestGap);
				Random r = problem.head.random;
				return list.get(r.nextInt(list.size()));
			}
		}

		// ************************************************************************
		// ***** Constraint SumSimpleGE
		// ************************************************************************

		public static class SumSimpleGE extends SumSimple implements TagGACGuaranteed, Optimizable {

			@Override
			public final boolean checkValues(int[] t) {
				return sum(t) >= limit;
			}

			@Override
			public long objectiveValue() {
				return currSum();
			}

			public SumSimpleGE(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, Math.max(limit, minPossibleSum(scp)));
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (min >= limit)
					return entailed();
				if (max < limit)
					return x == null ? false : x.dom.fail();
				for (int i = futvars.limit; i >= 0; i--) {
					Domain dom = scp[futvars.dense[i]].dom;
					if (dom.size() == 1)
						continue;
					min -= dom.firstValue();
					dom.removeValuesLT(limit - (max - dom.lastValue()));
					assert dom.size() > 0;
					min += dom.firstValue();
					if (min >= limit)
						return true;
				}
				return true;
			}
		}

		// ************************************************************************
		// ***** Constraint SumSimpleEQ
		// ************************************************************************

		public static final class SumSimpleEQ extends SumSimple {

			@Override
			public final boolean checkValues(int[] t) {
				return sum(t) == limit;
			}

			private boolean guaranteedGAC;

			public SumSimpleEQ(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
				this.guaranteedGAC = Stream.of(scp).allMatch(x -> x.dom.initSize() <= 2); // in this case, bounds consistency is GAC
			}

			@Override
			public boolean isGuaranteedAC() {
				return guaranteedGAC;
			}

			@Override
			public boolean runPropagator(Variable evt) {
				recomputeBounds();
				if (limit < min || max < limit)
					return evt.dom.fail();
				if (futvars.size() > 0) {
					int lastModified = futvars.limit, i = futvars.limit;
					do {
						Domain dom = scp[futvars.dense[i]].dom;
						int sizeBefore = dom.size();
						if (sizeBefore > 1) {
							min -= dom.firstValue();
							max -= dom.lastValue();
							if (dom.removeValuesLT(limit - max) == false || dom.removeValuesGT(limit - min) == false)
								return false;
							if (sizeBefore != dom.size())
								lastModified = i;
							min += dom.firstValue();
							max += dom.lastValue();
						}
						i = i > 0 ? i - 1 : futvars.limit; // cyclic iteration
					} while (lastModified != i);
				}
				assert controlFCLevel();
				return true;
			}

			public int deduce() { // experimental for infinite domains (to be finalized)
				Kit.control(futvars.size() == 1);
				int pos = futvars.dense[0];
				control(scp[pos].dom instanceof DomainInfinite);
				long sum = 0;
				for (int i = 0; i < scp.length; i++)
					if (i != pos)
						sum += scp[i].dom.uniqueValue();
				long res = limit - sum;
				Kit.control(Utilities.isSafeInt(res));
				return (int) res;
			}
		}

		// ************************************************************************
		// ***** Constraint SumSimpleNE
		// ************************************************************************

		public static final class SumSimpleNE extends SumSimple implements TagGACGuaranteed {

			@Override
			public final boolean checkValues(int[] t) {
				return sum(t) != limit;
			}

			private Variable sentinel1, sentinel2;

			public SumSimpleNE(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
				Kit.control(scp.length >= 2 && !Arrays.stream(scp).anyMatch(x -> x.dom.size() == 1));
				this.sentinel1 = scp[0];
				this.sentinel2 = scp[scp.length - 1];
			}

			private Variable findAnotherSentinel() {
				for (Variable x : scp)
					if (x != sentinel1 && x != sentinel2 && x.dom.size() > 1)
						return x;
				return null;
			}

			private boolean filterDomainOf(Variable sentinel) {
				assert sentinel.dom.size() > 1 && Stream.of(scp).filter(x -> x != sentinel).allMatch(x -> x.dom.size() == 1);
				long sum = 0;
				for (Variable x : scp)
					if (x != sentinel)
						sum += x.dom.uniqueValue(); // no overflow possible because int values are added to a long
				long v = limit - sum;
				if (sum + v == limit && Integer.MIN_VALUE <= v && v <= Integer.MAX_VALUE) // if no overflow and within Integer bounds
					sentinel.dom.removeValueIfPresent((int) v); // no inconsistency possible since at least two values in the domain
				return true;
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (sentinel1.dom.size() == 1) {
					Variable y = findAnotherSentinel();
					if (y == null)
						return sentinel2.dom.size() == 1 ? currSum() != limit || x.dom.fail() : filterDomainOf(sentinel2);
					sentinel1 = y;
				}
				// we know that from here, sentinel1 is a valid sentinel
				if (sentinel2.dom.size() == 1) {
					Variable y = findAnotherSentinel();
					if (y == null)
						return filterDomainOf(sentinel1); // since only the domain of sentinel1 is not singleton
					sentinel2 = y;
				}
				return true;
			}
		}

		// ************************************************************************
		// ***** Constraint SumSimpleEQBoolean (Is this class relevant (more efficient) ?
		// ************************************************************************

		public static final class SumSimpleEQBoolean extends SumSimple implements TagGACGuaranteed {

			@Override
			public final boolean checkValues(int[] t) {
				return sum(t) == limit;
			}

			public SumSimpleEQBoolean(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
				Kit.control(Variable.areAllInitiallyBoolean(scp));
			}

			@Override
			public boolean runPropagator(Variable x) {
				int cnt0 = 0, cnt1 = 0;
				for (Variable y : scp)
					if (y.dom.size() == 1)
						if (y.dom.unique() == 0)
							cnt0++;
						else
							cnt1++;
				int diff = scp.length - cnt0 - cnt1;
				if (cnt1 > limit || cnt1 + diff < limit)
					return x.dom.fail();
				if (cnt1 < limit && cnt1 + diff > limit)
					return true;
				if (cnt1 == limit) { // remove all 1
					for (int i = futvars.limit; i >= 0; i--) {
						Domain dom = scp[futvars.dense[i]].dom;
						if (dom.size() != 1)
							dom.removeSafely(1);
					}
				} else { // remove all 0
					assert cnt1 + diff == limit;
					for (int i = futvars.limit; i >= 0; i--) {
						Domain dom = scp[futvars.dense[i]].dom;
						if (dom.size() != 1)
							dom.removeSafely(0);
					}
				}
				return true;
			}
		}

	}

	/**********************************************************************************************
	 * SumWeighted
	 *********************************************************************************************/

	public static abstract class SumWeighted extends Sum {

		public static SumWeighted buildFrom(Problem pb, Variable[] vs, int[] coeffs, TypeConditionOperatorRel op, long limit) {
			switch (op) {
			case LT:
				return new SumWeightedLE(pb, vs, coeffs, limit - 1);
			case LE:
				return new SumWeightedLE(pb, vs, coeffs, limit);
			case GE:
				return new SumWeightedGE(pb, vs, coeffs, limit);
			case GT:
				return new SumWeightedGE(pb, vs, coeffs, limit + 1);
			case EQ:
				return new SumWeightedEQ(pb, vs, coeffs, limit);
			case NE:
				return new SumWeightedNE(pb, vs, coeffs, limit);
			}
			throw new AssertionError();
		}

		public static long weightedSum(int[] t, int[] coeffs) {
			assert t.length == coeffs.length;
			// note that no overflow control is performed here
			long sum = 0;
			for (int i = 0; i < t.length; i++)
				sum += coeffs[i] * t[i];
			return sum;
		}

		public static long minPossibleSum(Variable[] scp, int[] coeffs) {
			BigInteger sum = BigInteger.valueOf(0);
			for (int i = 0; i < scp.length; i++)
				sum = sum.add(BigInteger.valueOf(coeffs[i])
						.multiply(BigInteger.valueOf(coeffs[i] >= 0 ? scp[i].dom.toVal(0) : scp[i].dom.toVal(scp[i].dom.initSize() - 1))));
			return sum.longValueExact();
		}

		public static long maxPossibleSum(Variable[] scp, int[] coeffs) {
			BigInteger sum = BigInteger.valueOf(0);
			for (int i = 0; i < scp.length; i++)
				sum = sum.add(BigInteger.valueOf(coeffs[i])
						.multiply(BigInteger.valueOf(coeffs[i] >= 0 ? scp[i].dom.toVal(scp[i].dom.initSize() - 1) : scp[i].dom.toVal(0))));
			return sum.longValueExact();
		}

		public long minComputableObjectiveValue() {
			return minPossibleSum(scp, coeffs);
		}

		public long maxComputableObjectiveValue() {
			return maxPossibleSum(scp, coeffs);
		}

		public long minCurrentObjectiveValue() {
			long sum = 0;
			for (int i = 0; i < scp.length; i++)
				sum += coeffs[i] * (coeffs[i] >= 0 ? scp[i].dom.firstValue() : scp[i].dom.lastValue());
			return sum;
		}

		public long maxCurrentObjectiveValue() {
			long sum = 0;
			for (int i = 0; i < scp.length; i++)
				sum += coeffs[i] * (coeffs[i] >= 0 ? scp[i].dom.lastValue() : scp[i].dom.firstValue());
			return sum;
		}

		protected long currWeightedSum() {
			long sum = 0;
			for (int i = 0; i < scp.length; i++)
				sum += scp[i].dom.uniqueValue() * coeffs[i];
			return sum;
		}

		public final void limit(long newLimit) {
			super.limit(newLimit);
			if (coeffs != null) // not available at construction time
				control(minComputableObjectiveValue() - 1 <= limit && limit <= maxComputableObjectiveValue() + 1); // TODO using a cache for these two values
		}

		public final int[] coeffs;

		public SumWeighted(Problem pb, Variable[] scp, int[] coeffs, long limit) {
			super(pb, scp, limit);
			this.coeffs = coeffs;
			control(minComputableObjectiveValue() <= limit && limit <= maxComputableObjectiveValue());
			defineKey(Kit.join(coeffs), limit);
			control(IntStream.range(0, coeffs.length).allMatch(i -> coeffs[i] != 0 && (i == 0 || coeffs[i - 1] <= coeffs[i])));
			control(minComputableObjectiveValue() <= maxComputableObjectiveValue()); // Important: we check this way that no overflow is possible
		}

		@Override
		public int[] defineSymmetryMatching() {
			int[] symmetryMatching = new int[scp.length];
			int color = 1;
			for (int i = 0; i < symmetryMatching.length; i++) {
				if (symmetryMatching[i] != 0)
					continue;
				for (int j = i + 1; j < symmetryMatching.length; j++)
					if (symmetryMatching[j] == 0 && coeffs[i] == coeffs[j])
						symmetryMatching[j] = color;
				symmetryMatching[i] = color++;
			}
			return symmetryMatching;
		}

		protected void recomputeBounds() {
			min = max = 0;
			for (int i = 0; i < scp.length; i++) {
				Domain dom = scp[i].dom;
				int coeff = coeffs[i];
				min += coeff * (coeff >= 0 ? dom.firstValue() : dom.lastValue());
				max += coeff * (coeff >= 0 ? dom.lastValue() : dom.firstValue());
			}
		}

		// ************************************************************************
		// ***** Constraint SumWeightedLE
		// ************************************************************************

		public static final class SumWeightedLE extends SumWeighted implements TagGACGuaranteed, Optimizable {

			@Override
			public boolean checkValues(int[] t) {
				return weightedSum(t, coeffs) <= limit;
			}

			@Override
			public long objectiveValue() {
				return currWeightedSum();
			}

			public SumWeightedLE(Problem pb, Variable[] scp, int[] coeffs, long limit) {
				super(pb, scp, coeffs, Math.min(limit, maxPossibleSum(scp, coeffs)));
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (max <= limit) {
					entailed();
					return true;
				}
				if (min > limit)
					return x == null ? false : x.dom.fail();
				for (int i = futvars.limit; i >= 0; i--) {
					Domain dom = scp[futvars.dense[i]].dom;
					if (dom.size() == 1)
						continue;
					int coeff = coeffs[futvars.dense[i]];
					if (coeff >= 0) {
						max -= dom.lastValue() * coeff;
						dom.removeValues(GT, limit - (min - dom.firstValue() * coeff), coeff);
						assert dom.size() > 0;
						max += dom.lastValue() * coeff;
					} else {
						max -= dom.firstValue() * coeff;
						dom.removeValues(GT, limit - (min - dom.lastValue() * coeff), coeff);
						assert dom.size() > 0;
						max += dom.firstValue() * coeff;
					}
					if (max <= limit)
						return true;
				}
				return true;
			}
		}

		// ************************************************************************
		// ***** Constraint SumWeightedGE
		// ************************************************************************

		public static class SumWeightedGE extends SumWeighted implements TagGACGuaranteed, Optimizable {

			@Override
			public boolean checkValues(int[] t) {
				return weightedSum(t, coeffs) >= limit;
			}

			@Override
			public long objectiveValue() {
				return currWeightedSum();
			}

			public SumWeightedGE(Problem pb, Variable[] scp, int[] coeffs, long limit) {
				super(pb, scp, coeffs, Math.max(limit, minPossibleSum(scp, coeffs)));
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (min >= limit) {
					entailed();
					return true;
				}
				if (max < limit)
					return x == null ? false : x.dom.fail();
				for (int i = futvars.limit; i >= 0; i--) {
					Domain dom = scp[futvars.dense[i]].dom;
					if (dom.size() == 1)
						continue;
					int coeff = coeffs[futvars.dense[i]];
					if (coeff >= 0) {
						min -= dom.firstValue() * coeff;
						dom.removeValues(LT, limit - (max - dom.lastValue() * coeff), coeff);
						assert dom.size() > 0;
						min += dom.firstValue() * coeff;
					} else {
						min -= dom.lastValue() * coeff;
						dom.removeValues(LT, limit - (max - dom.firstValue() * coeff), coeff);
						assert dom.size() > 0;
						min += dom.lastValue() * coeff;
					}
					if (min >= limit)
						return true;
				}
				return true;
			}

		}

		// ************************************************************************
		// ***** Constraint SumWeightedEQ
		// ************************************************************************

		public static final class SumWeightedEQ extends SumWeighted {

			@Override
			public boolean checkValues(int[] t) {
				return weightedSum(t, coeffs) == limit;
			}

			private boolean guaranteedGAC;

			public SumWeightedEQ(Problem pb, Variable[] scp, int[] coeffs, long limit) {
				super(pb, scp, coeffs, limit);
				this.guaranteedGAC = Stream.of(scp).allMatch(x -> x.dom.initSize() <= 2); // in this case, bounds consistency is GAC
			}

			@Override
			public boolean isGuaranteedAC() {
				return guaranteedGAC;
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (min > limit || max < limit)
					return x.dom.fail();
				if (futvars.size() > 0) {
					int lastModified = futvars.limit, i = futvars.limit;
					do {
						Domain dom = scp[futvars.dense[i]].dom;
						int sizeBefore = dom.size();
						if (sizeBefore > 1) {
							int coeff = coeffs[futvars.dense[i]];
							min -= coeff * (coeff >= 0 ? dom.firstValue() : dom.lastValue());
							max -= coeff * (coeff >= 0 ? dom.lastValue() : dom.firstValue());
							if (dom.removeValues(LT, limit - max, coeff) == false || dom.removeValues(GT, limit - min, coeff) == false)
								return false;
							if (sizeBefore != dom.size())
								lastModified = i;
							min += coeff * (coeff >= 0 ? dom.firstValue() : dom.lastValue());
							max += coeff * (coeff >= 0 ? dom.lastValue() : dom.firstValue());
						}
						i = i > 0 ? i - 1 : futvars.limit; // cyclic iteration
					} while (lastModified != i);
				}
				assert controlFCLevel();
				return true;
			}

			int cnt = 0;

			public int deduce() { // experimental for infinite domains (to be finalized)
				Kit.control(futvars.size() == 1);
				int pos = futvars.dense[0];
				control(scp[pos].dom instanceof DomainInfinite, " " + scp[pos]);
				long sum = 0;
				for (int i = 0; i < scp.length; i++)
					if (i != pos)
						sum += scp[i].dom.uniqueValue() * coeffs[i];
				control((limit - sum) % coeffs[pos] == 0);
				long res = (limit - sum) / coeffs[pos];
				control(Utilities.isSafeInt(res));
				// pb.solver.pushVariable(scp[pos]);
				scp[pos].dom.reduceTo((int) res); // , pb.solver.depth());
				return (int) res;
			}
		}

		// ************************************************************************
		// ***** Constraint SumWeightedNE
		// ************************************************************************

		public static final class SumWeightedNE extends SumWeighted implements TagGACGuaranteed {

			@Override
			public boolean checkValues(int[] t) {
				return weightedSum(t, coeffs) != limit;
			}

			private Variable sentinel1, sentinel2;

			public SumWeightedNE(Problem pb, Variable[] scp, int[] coeffs, long limit) {
				super(pb, scp, coeffs, limit);
				control(scp.length >= 2 && !Arrays.stream(scp).anyMatch(x -> x.dom.size() == 1));
				this.sentinel1 = scp[0];
				this.sentinel2 = scp[scp.length - 1];
			}

			private Variable findAnotherSentinel() {
				for (Variable x : scp)
					if (x != sentinel1 && x != sentinel2 && x.dom.size() > 1)
						return x;
				return null;
			}

			private boolean filterDomainOf(Variable sentinel) {
				assert sentinel.dom.size() > 1 && Stream.of(scp).filter(x -> x != sentinel).allMatch(x -> x.dom.size() == 1);
				int p = -1; // position of sentinel
				long sum = 0;
				for (int i = 0; i < scp.length; i++)
					if (scp[i] != sentinel)
						sum += scp[i].dom.uniqueValue() * coeffs[i]; // no overflow possible because it was controlled at construction
					else
						p = i;
				long v = (limit - sum) / coeffs[p];
				control(v * coeffs[p] + sum == limit);
				if ((limit - sum) % coeffs[p] == 0 && Integer.MIN_VALUE <= v && v <= Integer.MAX_VALUE)
					sentinel.dom.removeValueIfPresent((int) v); // no inconsistency possible since at least two values
				return true;
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (sentinel1.dom.size() == 1) {
					Variable y = findAnotherSentinel();
					if (y == null)
						return sentinel2.dom.size() == 1 ? currWeightedSum() != limit || x.dom.fail() : filterDomainOf(sentinel2);
					sentinel1 = y;
				}
				// we know that from here, sentinel1 is a valid sentinel
				if (sentinel2.dom.size() == 1) {
					Variable y = findAnotherSentinel();
					if (y == null)
						return filterDomainOf(sentinel1); // since only the domain at sentinel1 is not singleton
					sentinel2 = y;
				}
				return true;
			}
		}

	}

}
