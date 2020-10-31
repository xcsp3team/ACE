/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import static org.xcsp.common.Types.TypeOperatorRel.GT;
import static org.xcsp.common.Types.TypeOperatorRel.LT;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;

import interfaces.Optimizable;
import interfaces.TagGACGuaranteed;
import problem.Problem;
import utility.Kit;
import utility.exceptions.UnreachableCodeException;
import variables.Variable;
import variables.domains.Domain;
import variables.domains.DomainHuge;

public abstract class SumWeighted extends SumAbstract {

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
		throw new UnreachableCodeException();
	}

	public long minComputableObjectiveValue() {
		BigInteger sum = BigInteger.valueOf(0);
		for (int i = 0; i < scp.length; i++)
			sum = sum.add(BigInteger.valueOf(coeffs[i])
					.multiply(BigInteger.valueOf(coeffs[i] >= 0 ? scp[i].dom.toVal(0) : scp[i].dom.toVal(scp[i].dom.initSize() - 1))));
		return sum.longValueExact();
	}

	public long maxComputableObjectiveValue() {
		BigInteger sum = BigInteger.valueOf(0);
		for (int i = 0; i < scp.length; i++)
			sum = sum.add(BigInteger.valueOf(coeffs[i])
					.multiply(BigInteger.valueOf(coeffs[i] >= 0 ? scp[i].dom.toVal(scp[i].dom.initSize() - 1) : scp[i].dom.toVal(0))));
		return sum.longValueExact();
	}

	public final int[] coeffs;

	public SumWeighted(Problem pb, Variable[] scp, int[] coeffs, long limit) {
		super(pb, scp, limit);
		this.coeffs = coeffs;
		defineKey(Kit.join(coeffs), limit);
		Kit.control(IntStream.range(0, coeffs.length).allMatch(i -> coeffs[i] != 0 && (i == 0 || coeffs[i - 1] <= coeffs[i])));
		Kit.control(minComputableObjectiveValue() <= maxComputableObjectiveValue()); // Important: we check this way that no overflow is possible
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

	protected long currWeightedSum() {
		long sum = 0;
		for (int i = 0; i < scp.length; i++)
			sum += scp[i].dom.uniqueValue() * coeffs[i];
		return sum;
	}

	// ************************************************************************
	// ***** Constraint SumWeightedLE
	// ************************************************************************

	public static final class SumWeightedLE extends SumWeighted implements TagGACGuaranteed, Optimizable {

		@Override
		public boolean checkValues(int[] t) {
			return Kit.weightedSum(t, coeffs) <= limit;
		}

		@Override
		public long objectiveValue() {
			return currWeightedSum();
		}

		public SumWeightedLE(Problem pb, Variable[] scp, int[] coeffs, long limit) {
			super(pb, scp, coeffs, limit);
		}

		@Override
		public boolean runPropagator(Variable x) {
			recomputeBounds();
			if (max <= limit)
				return true;
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
			return Kit.weightedSum(t, coeffs) >= limit;
		}

		@Override
		public long objectiveValue() {
			return currWeightedSum();
		}

		public SumWeightedGE(Problem pb, Variable[] scp, int[] coeffs, long limit) {
			super(pb, scp, coeffs, limit);
		}

		@Override
		public boolean runPropagator(Variable x) {
			recomputeBounds();
			if (min >= limit)
				return true;
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
			return Kit.weightedSum(t, coeffs) == limit;
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

		public int deduce() {
			Kit.control(futvars.size() == 1);
			int pos = futvars.dense[0];
			Kit.control(scp[pos].dom instanceof DomainHuge, () -> " " + scp[pos]);
			long sum = 0;
			for (int i = 0; i < scp.length; i++)
				if (i != pos)
					sum += scp[i].dom.uniqueValue() * coeffs[i];
			Kit.control((limit - sum) % coeffs[pos] == 0);
			long res = (limit - sum) / coeffs[pos];
			Kit.control(Utilities.isSafeInt(res));
			// if (cnt++ % 1000 == 0)
			// System.out.println("dudicung " + scp[pos] + " = " + res);
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
			return Kit.weightedSum(t, coeffs) != limit;
		}

		private Variable sentinel1, sentinel2;

		public SumWeightedNE(Problem pb, Variable[] scp, int[] coeffs, long limit) {
			super(pb, scp, coeffs, limit);
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
			int p = -1; // position of sentinel
			long sum = 0;
			for (int i = 0; i < scp.length; i++)
				if (scp[i] != sentinel)
					sum += scp[i].dom.uniqueValue() * coeffs[i]; // no overflow possible because it was controlled at construction
				else
					p = i;
			long v = (limit - sum) / coeffs[p];
			Kit.control(v * coeffs[p] + sum == limit);
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
