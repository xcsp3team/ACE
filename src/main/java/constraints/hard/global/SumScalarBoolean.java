/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import java.util.stream.IntStream;

import org.xcsp.common.Types.TypeConditionOperatorRel;

import constraints.hard.CtrGlobal;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import problem.Problem;
import utility.exceptions.UnreachableCodeException;
import utility.sets.SetDense;
import variables.Variable;
import variables.domains.Domain;

public abstract class SumScalarBoolean extends CtrGlobal {

	protected final Variable[] list;
	protected final Variable[] coeffs;

	protected final int half; // number of terms (products) on the left

	protected long min, max; // used to store computed bounds when filtering
	protected final SetDense set01vs1; // used to store the indexes of terms such that one variable has domain {0,1} and the other domain {1}

	public SumScalarBoolean(Problem pb, Variable[] list, Variable[] coeffs, Variable limit) {
		super(pb, pb.api.vars(list, coeffs, limit)); // limit is null if the object is from a subclass of SumScalarBooleanCst
		this.list = list;
		this.coeffs = coeffs;
		this.half = list.length;
		this.set01vs1 = new SetDense(half);
		assert list.length == coeffs.length && Variable.areAllInitiallyBoolean(pb.api.vars(list, coeffs));
	}

	public SumScalarBoolean(Problem pb, Variable[] list, Variable[] coeffs) {
		this(pb, list, coeffs, null);
	}

	protected int sum(int[] t) {
		return IntStream.range(0, half).map(i -> t[i] * t[half + i]).sum();
	}

	protected void recomputeBounds() {
		min = max = 0;
		set01vs1.clear();
		for (int i = 0; i < half; i++) {
			Domain dom1 = scp[i].dom, dom2 = scp[i + half].dom;
			if (dom1.isPresent(1) && dom2.isPresent(1)) { // if one 1 is missing nothing to do because the product is necessarily 0
				max++;
				if (!dom1.isPresent(0) && !dom2.isPresent(0))
					min++;
				else if (dom1.size() == 1 || dom2.size() == 1)
					set01vs1.add(i); // we add i iff we have (0,1) versus 1 (or equivalently 1 versus (0,1)) ; the only way to filter here
			}
		}
	}

	protected void removeFrom01vs1(int value) {
		assert value == 0 || value == 1;
		for (int i = set01vs1.limit; i >= 0; i--) {
			int j = set01vs1.dense[i];
			assert (scp[j].dom.size() == 2 && scp[half + j].dom.onlyContains(1)) || (scp[half + j].dom.size() == 2 && scp[j].dom.onlyContains(1));
			if (scp[j].dom.size() == 2)
				scp[j].dom.remove(value);
			else
				scp[half + j].dom.remove(value);
		}
	}

	// ************************************************************************
	// ***** Constraint SumScalarBooleanCst
	// ************************************************************************

	public static abstract class SumScalarBooleanCst extends SumScalarBoolean implements TagGACGuaranteed, TagFilteringCompleteAtEachCall {

		public static SumScalarBooleanCst buildFrom(Problem pb, Variable[] list, Variable[] coeffs, TypeConditionOperatorRel op, int limit) {
			switch (op) {
			case LT:
				return new SumScalarBooleanLE(pb, list, coeffs, limit - 1);
			case LE:
				return new SumScalarBooleanLE(pb, list, coeffs, limit);
			case GE:
				return new SumScalarBooleanGE(pb, list, coeffs, limit);
			case GT:
				return new SumScalarBooleanGE(pb, list, coeffs, limit + 1);
			case EQ:
				return new SumScalarBooleanEQ(pb, list, coeffs, limit);
			default:
				throw new UnreachableCodeException("NE is not implemented"); // TODO useful to have a propagator ?
			}
		}

		protected int limit;

		public SumScalarBooleanCst(Problem pb, Variable[] list, Variable[] coeffs, int limit) {
			super(pb, list, coeffs);
			this.limit = limit;
		}

		public static final class SumScalarBooleanLE extends SumScalarBooleanCst {

			@Override
			public boolean checkValues(int[] t) {
				return sum(t) <= limit;
			}

			public SumScalarBooleanLE(Problem pb, Variable[] list, Variable[] coeffs, int limit) {
				super(pb, list, coeffs, limit);
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (max <= limit)
					return true;
				if (min > limit)
					return x.dom.fail();
				if (min == limit) // this is the only case where we can filter
					removeFrom01vs1(1);
				return true;
			}
		}

		public static final class SumScalarBooleanGE extends SumScalarBooleanCst {

			@Override
			public boolean checkValues(int[] t) {
				return sum(t) >= limit;
			}

			public SumScalarBooleanGE(Problem pb, Variable[] list, Variable[] coeffs, int limit) {
				super(pb, list, coeffs, limit);
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (min >= limit)
					return true;
				if (max < limit)
					return x.dom.fail();
				if (max == limit) // this is the only case where we can filter
					removeFrom01vs1(0);
				return true;
			}
		}

		public static final class SumScalarBooleanEQ extends SumScalarBooleanCst {

			@Override
			public boolean checkValues(int[] t) {
				return sum(t) == limit;
			}

			private SetDense set01vs01;

			public SumScalarBooleanEQ(Problem pb, Variable[] list, Variable[] coeffs, int limit) {
				super(pb, list, coeffs, limit);
				this.set01vs01 = new SetDense(half);
			}

			@Override
			protected void recomputeBounds() {
				min = max = 0;
				set01vs1.clear();
				set01vs01.clear();
				for (int i = 0; i < half; i++) {
					Domain dom1 = scp[i].dom, dom2 = scp[i + half].dom;
					if (dom1.isPresent(1) && dom2.isPresent(1)) { // if one 1 is missing nothing to do because the product is necessarily 0
						max++;
						if (!dom1.isPresent(0) && !dom2.isPresent(0))
							min++;
						else if (dom1.size() == 1 || dom2.size() == 1)
							set01vs1.add(i); // we add i iff we have (0,1) versus 1 (or equivalently 1 versus (0,1))
						else
							set01vs01.add(i); // we add i because we have (0,1) versus (0,1)
					}
				}
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (min > limit || max < limit)
					return x.dom.fail();
				if (min == max || (min < limit && limit < max))
					return true; // because entailed in that case
				if (min == limit) {
					removeFrom01vs1(1);
				} else if (max == limit) {
					removeFrom01vs1(0);
					for (int i = set01vs01.limit; i >= 0; i--) {
						int j = set01vs01.dense[i];
						assert (scp[j].dom.size() == 2 && scp[half + j].dom.size() == 2);
						scp[j].dom.remove(0);
						scp[half + j].dom.remove(0);
					}
				}
				return true;
			}
		}
	}
	// ************************************************************************
	// ***** Constraint SumScalarBooleanVar
	// ************************************************************************

	public static abstract class SumScalarBooleanVar extends SumScalarBoolean implements TagGACGuaranteed, TagFilteringCompleteAtEachCall {

		public static SumScalarBooleanVar buildFrom(Problem pb, Variable[] list, Variable[] coeffs, TypeConditionOperatorRel op, Variable limit) {
			switch (op) {
			case LT:
				return new SumScalarBooleanVarLE(pb, list, coeffs, pb.replaceByVariable(pb.api.sub(limit, 1)));
			case LE:
				return new SumScalarBooleanVarLE(pb, list, coeffs, limit);
			case GE:
				return new SumScalarBooleanVarGE(pb, list, coeffs, limit);
			case GT:
				return new SumScalarBooleanVarLE(pb, list, coeffs, pb.replaceByVariable(pb.api.add(limit, 1)));
			default:
				throw new UnreachableCodeException("NE and EQ are not implemented"); // TODO useful to have propagators
			}
		}

		protected Variable limit;

		public SumScalarBooleanVar(Problem pb, Variable[] list, Variable[] coeffs, Variable limit) {
			super(pb, list, coeffs, limit);
			this.limit = limit;
		}

		public static final class SumScalarBooleanVarLE extends SumScalarBooleanVar {

			@Override
			public boolean checkValues(int[] t) {
				return sum(t) <= t[t.length - 1];
			}

			public SumScalarBooleanVarLE(Problem pb, Variable[] list, Variable[] coeffs, Variable limit) {
				super(pb, list, coeffs, limit);
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (!limit.dom.removeValuesLessThan(min))
					return false;
				int vlimit = limit.dom.lastValue();
				if (max <= vlimit)
					return true;
				if (min == vlimit) { // this is the only case where we can filter
					assert limit.dom.size() == 1;
					removeFrom01vs1(1);
				}
				return true;
			}
		}

		public static final class SumScalarBooleanVarGE extends SumScalarBooleanVar {

			@Override
			public boolean checkValues(int[] t) {
				return sum(t) >= t[t.length - 1];
			}

			public SumScalarBooleanVarGE(Problem pb, Variable[] list, Variable[] coeffs, Variable limit) {
				super(pb, list, coeffs, limit);
			}

			@Override
			public boolean runPropagator(Variable x) {
				recomputeBounds();
				if (!limit.dom.removeValuesGreaterThan(max))
					return false;
				int vlimit = limit.dom.firstValue();
				if (min >= vlimit)
					return true;
				if (max == vlimit) { // this is the only case where we can filter
					assert limit.dom.size() == 1;
					removeFrom01vs1(0);
				}
				return true;
			}
		}
	}
}
