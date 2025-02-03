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

import java.math.BigInteger;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeConditionOperatorRel;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * This is the root class for any constraint Product. This kind of constraints is clearly less frequent than Sum.
 * Currently, there are three subclasses.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Product extends ConstraintGlobal implements TagCallCompleteFiltering {

	/**
	 * The limit (right-hand term) of the constraint
	 */
	protected long limit;

	/**
	 * The minimal product (of the left-hand expression) that can be computed at a given moment; used during filtering
	 * in most of the subclasses
	 */
	protected long min;

	/**
	 * The maximal product (of the left-hand expression) that can be computed at a given moment; used during filtering
	 * in most of the subclasses
	 */
	protected long max;

	/**
	 * The minimal product (of the left-hand expression) that can be computed at a given moment, when excluding
	 * variables whose domains contain 0.
	 */
	protected long minWithout0;

	/**
	 * Builds a constraint Product for the specified problem, and with the specified scope
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public Product(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length > 1);
	}

	/**********************************************************************************************
	 * ProductSimple
	 *********************************************************************************************/

	/**
	 * Root class for managing simple Product constraints. Currently, the code is valid only for integer variables with
	 * positive domains, i.e., domains containing no negative value.
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
			default: // case NE:
				throw new AssertionError("NE not implemented");
			}
		}

		/**
		 * @param t
		 *            an array of integers
		 * @return the product of the values in the specified array
		 */
		public static final long product(int[] t) {
			long l = 1;
			for (int v : t)
				l *= v;
			return l;
		}

		/**
		 * Returns the product of the values currently assigned to the variables in the scope. IMPORTANT: all variables
		 * must be assigned.
		 * 
		 * @return the product of the values currently assigned to the variables in the scope.
		 */
		protected final long currProduct() {
			long sum = 0;
			for (Variable x : scp)
				sum *= x.dom.singleValue();
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

		/**
		 * Remove 0 from the domain of every variable in the scope (if present). IMPORTANT: must be only called at
		 * construction time.
		 */
		protected void remove0() {
			for (Domain dom : doms)
				if (dom.containsValue(0))
					dom.removeValueAtConstructionTime(0);
		}

		/**
		 * Recomputes the minimal and maximal sums (seen as bounds) that can be obtained with respect to the current
		 * domains of the involved variables.
		 * 
		 * @return the number of variables with 0 in their domains
		 */
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

		public static final class ProductSimpleLE extends ProductSimple implements TagAC {

			@Override
			public final boolean isSatisfiedBy(int[] t) {
				return product(t) <= limit;
			}

			public ProductSimpleLE(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
				if (limit < 0)
					remove0();
			}

			@Override
			public boolean runPropagator(Variable x) {
				int n0 = recomputeBounds();
				if (max <= limit)
					return entail();
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
					else if (dom.firstValue() == 0 && n0 == 1) {
						// otherwise another variable has 0 as first value (and so no filtering is possible)
						dom.removeValuesGT(limit / minWithout0);
					}
					assert dom.size() > 0;
					max = max * dom.lastValue();
					if (max <= limit)
						return entail();
				}
				return true;
			}
		}

		// ************************************************************************
		// ***** Constraint ProductSimpleGE
		// ************************************************************************

		public static final class ProductSimpleGE extends ProductSimple implements TagAC {

			@Override
			public final boolean isSatisfiedBy(int[] t) {
				return product(t) >= limit;
			}

			public ProductSimpleGE(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
				if (limit > 0)
					remove0();
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (min >= limit)
					return entail();
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
						return entail();
				}
				return true;
			}
		}

		// ************************************************************************
		// ***** Constraint ProductSimpleEQ
		// ************************************************************************

		public static final class ProductSimpleEQ extends ProductSimple implements TagNotAC {

			@Override
			public final boolean isSatisfiedBy(int[] t) {
				return product(t) == limit;
			}

			public ProductSimpleEQ(Problem pb, Variable[] scp, long limit) {
				super(pb, scp, limit);
				if (limit != 0)
					remove0();
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (limit < min || limit > max)
					return x.dom.fail();
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
