/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;

import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagSymmetric;
import optimization.Optimizable;
import problem.Problem;
import utility.Kit;
import variables.Domain;
import variables.DomainInfinite;
import variables.Variable;

/**
 * Root class for managing simple sum constraints (i.e., sum constraints without integer coefficients associated with variables). Note that no overflow is
 * possible because all sum of integer values (int) cannot exceed long values.
 * 
 * @author lecoutre
 *
 */
public abstract class SumSimple extends Sum implements TagSymmetric {

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

	static long minPossibleSum(Variable[] scp) {
		long sum = 0;
		for (Variable x : scp)
			sum += x.dom.toVal(0);
		return sum;
	}

	static long maxPossibleSum(Variable[] scp) {
		long sum = 0;
		for (Variable x : scp)
			sum += x.dom.toVal(x.dom.initSize() - 1);
		return sum;
	}

	public long minComputableObjectiveValue() {
		return minPossibleSum(scp);
	}

	public long maxComputableObjectiveValue() {
		return maxPossibleSum(scp);
	}

	public long minCurrentObjectiveValue() {
		long sum = 0;
		for (Variable x : scp)
			sum += x.dom.firstValue();
		return sum;
	}

	public long maxCurrentObjectiveValue() {
		long sum = 0;
		for (Variable x : scp)
			sum += x.dom.lastValue();
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

	protected void recomputeBounds() {
		min = max = 0;
		for (Variable x : scp) {
			min += x.dom.firstValue();
			max += x.dom.lastValue();
		}
	}

	protected final long currSum() {
		long sum = 0;
		for (Variable x : scp)
			sum += x.dom.uniqueValue();
		return sum;
	}

	// ************************************************************************
	// ***** Constraint SumSimpleLE
	// ************************************************************************

	public static class SumSimpleLE extends SumSimple implements TagGACGuaranteed, Optimizable {

		@Override
		public final boolean checkValues(int[] t) {
			return sum(t) <= limit;
		}

		// @Override
		// public void restoreBefore(int depth) {
		// if (entailedLevel == depth)
		// entailedLevel = -1;
		// }

		@Override
		public long objectiveValue() {
			return currSum();
		}

		public SumSimpleLE(Problem pb, Variable[] scp, long limit) {
			super(pb, scp, Math.min(limit, maxPossibleSum(scp)));
		}

		int cnt = 0;

		@Override
		public boolean runPropagator(Variable x) {
			// if (problem.optimizer.ctr == this)
			// System.out.println(cnt++);
			recomputeBounds();
			if (max <= limit) {
				entailed(); // Level = problem.solver.depth();
				return true;
			}
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

		public Variable mostImpacting() {
			int[] solution = problem.solver.solManager.lastSolution;
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

		// @Override
		// public void restoreBefore(int depth) {
		// if (entailedLevel == depth)
		// entailedLevel = -1;
		// }

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
			if (min >= limit) {
				entailed(); // Level = problem.solver.depth();
				return true;
			}
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
