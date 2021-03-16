/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.math.BigInteger;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeConditionOperatorRel;

import constraints.Constraint.CtrGlobal;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import variables.Domain;
import variables.Variable;

public abstract class Product extends CtrGlobal implements TagFilteringCompleteAtEachCall {

	protected long limit;

	protected long min, max; // used in most of the subclasses

	protected long minWithout0;

	public Product(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length > 1);
	}

	/**********************************************************************************************
	 * ProductSimple
	 *********************************************************************************************/

	/**
	 * Root class for managing simple sum constraints (i.e., sum constraints without integer coefficients associated with variables). Note that no overflow is
	 * possible because all sum of integer values (int) cannot exceed long values.
	 */
	public static abstract class ProductSimple extends Product implements TagSymmetric {

		public static ProductSimple buildFrom(Problem pb, Variable[] scp, TypeConditionOperatorRel op, long limit) {
			switch (op) {
			case LT:
				return new ProductSimpleLE(pb, scp, limit - 1);
			case LE:
				return new ProductSimpleLE(pb, scp, limit);
			case GE:
				return new ProductSimpleGE(pb, scp, limit);
			case GT:
				return new ProductSimpleGE(pb, scp, limit + 1);
			case EQ:
				return new ProductSimpleEQ(pb, scp, limit);
			case NE:
				throw new AssertionError(); // not implemented for the moment
			}
			throw new AssertionError();
		}

		protected final long product(int[] t) {
			long l = 1;
			for (int v : t)
				l *= v;
			return l;
		}

		protected final long currProduct() {
			long sum = 0;
			for (Variable x : scp)
				sum *= x.dom.uniqueValue();
			return sum;
		}

		private long maxCurrentProduct(Variable[] scp) {
			assert Stream.of(scp).allMatch(x -> x.dom.firstValue() >= 0);
			BigInteger product = BigInteger.valueOf(1);
			for (int i = 0; i < scp.length; i++)
				product = product.multiply(BigInteger.valueOf(scp[i].dom.lastValue()));
			return product.longValueExact();
		}

		public ProductSimple(Problem pb, Variable[] scp, long limit) {
			super(pb, scp);
			control(limit > 0 && Stream.of(scp).allMatch(x -> x.dom.firstValue() >= 0), " for the moment, only positive values");
			maxCurrentProduct(scp); // to control that we have no overflow
			this.limit = limit;
		}

		protected final int recomputeBounds() {
			int n0 = 0;
			min = max = minWithout0 = 1;
			for (Domain dom : doms) {
				min *= dom.firstValue();
				max *= dom.lastValue();
				if (dom.firstValue() == 0)
					n0++;
				else
					minWithout0 *= dom.firstValue();
			}
			return n0;
		}

		// ************************************************************************
		// ***** Constraint ProductSimpleLE
		// ************************************************************************

		public static class ProductSimpleLE extends ProductSimple implements TagGACGuaranteed {

			@Override
			public final boolean checkValues(int[] t) {
				return product(t) <= limit;
			}

			public ProductSimpleLE(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
			}

			@Override
			public boolean runPropagator(Variable x) {
				int n0 = recomputeBounds();
				if (max <= limit)
					return entailed();
				if (min > limit)
					return x == null ? false : x.dom.fail();
				for (int i = futvars.limit; i >= 0; i--) {
					Domain dom = scp[futvars.dense[i]].dom;
					if (dom.size() == 1)
						continue;
					assert max != 0;
					max = max / dom.lastValue();
					if (min != 0)
						dom.removeValuesGT(limit / (min / dom.firstValue()));
					else if (dom.firstValue() == 0) { // otherwise another variable has 0 as first value (and so no filtering is possible)
						if (n0 == 1)
							dom.removeValuesGT(limit / minWithout0);
					}
					assert dom.size() > 0;
					max = max * dom.lastValue();
					if (max <= limit)
						return entailed();
				}
				return true;
			}
		}

		// ************************************************************************
		// ***** Constraint ProductSimpleGE
		// ************************************************************************

		public static class ProductSimpleGE extends ProductSimple implements TagGACGuaranteed {

			@Override
			public final boolean checkValues(int[] t) {
				return product(t) >= limit;
			}

			public ProductSimpleGE(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
				for (Domain dom : doms)
					if (dom.presentValue(0))
						dom.removeValueAtConstructionTime(0); // because limit is assumed to be > 0
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
					min = min / dom.firstValue();
					dom.removeValuesLT(limit / (max / dom.lastValue()));
					assert dom.size() > 0;
					min = min * dom.firstValue();
					if (min >= limit)
						return entailed();
				}
				return true;
			}
		}

		// ************************************************************************
		// ***** Constraint ProductSimpleEQ
		// ************************************************************************

		public static final class ProductSimpleEQ extends ProductSimple {

			@Override
			public final boolean checkValues(int[] t) {
				return product(t) == limit;
			}

			public ProductSimpleEQ(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
				for (Domain dom : doms)
					if (dom.presentValue(0))
						dom.removeValueAtConstructionTime(0); // because limit is assumed to be > 0
			}

			@Override
			public boolean isGuaranteedAC() {
				return false; // guaranteedGAC;
			}

			@Override
			public boolean runPropagator(Variable evt) {
				recomputeBounds();
				if (limit < min || limit > max)
					return evt.dom.fail();
				if (futvars.size() > 0) {
					int lastModified = futvars.limit, i = futvars.limit;
					do {
						Domain dom = scp[futvars.dense[i]].dom;
						int sizeBefore = dom.size();
						if (sizeBefore > 1) {
							min = min / dom.firstValue();
							max = max / dom.lastValue();
							if (dom.removeValuesLT(limit / max) == false || dom.removeValuesGT(limit / min) == false)
								return false;
							if (sizeBefore != dom.size())
								lastModified = i;
							min = min * dom.firstValue();
							max = max * dom.lastValue();
						}
						i = i > 0 ? i - 1 : futvars.limit; // cyclic iteration
					} while (lastModified != i);
				}
				return true;
			}
		}

	}
}
