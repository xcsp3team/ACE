/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.stream.IntStream;

import org.xcsp.common.Types.TypeOperatorRel;

import constraints.Constraint.CtrGlobal;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagUnsymmetric;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public abstract class Ordered extends CtrGlobal implements TagGACGuaranteed, TagFilteringCompleteAtEachCall, TagUnsymmetric {

	public static Ordered build(Problem pb, Variable[] x, int[] lengths, TypeOperatorRel op) {
		switch (op) {
		case LT:
			return new OrderedLT(pb, x, lengths);
		case LE:
			return new OrderedLE(pb, x, lengths);
		case GE:
			return new OrderedGE(pb, x, lengths);
		default: // GT
			return new OrderedGT(pb, x, lengths);
		}
	}

	protected int[] lengths;

	public Ordered(Problem pb, Variable[] scp, int[] lengths) {
		super(pb, scp);
		this.lengths = lengths;
		Kit.control(scp.length == lengths.length + 1);
	}

	public Ordered(Problem pb, Variable[] scp) {
		this(pb, scp, new int[scp.length - 1]);
	}

	public static final class OrderedLT extends Ordered {

		@Override
		public final boolean checkValues(int[] t) {
			return IntStream.range(0, t.length - 1).allMatch(i -> t[i] + lengths[i] < t[i + 1]);
		}

		public OrderedLT(Problem pb, Variable[] scp, int[] lengths) {
			super(pb, scp, lengths);
		}

		public OrderedLT(Problem pb, Variable[] scp) {
			super(pb, scp);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			for (int i = scp.length - 2; i >= 0; i--)
				if (!scp[i].dom.removeValuesGE(scp[i + 1].dom.lastValue() - lengths[i]))
					return false;
			for (int i = 0; i < scp.length - 1; i++)
				if (!scp[i + 1].dom.removeValuesLE(scp[i].dom.firstValue() + lengths[i]))
					return false;
			return true;
		}

	}

	public static final class OrderedLE extends Ordered {

		@Override
		public final boolean checkValues(int[] t) {
			return IntStream.range(0, t.length - 1).allMatch(i -> t[i] + lengths[i] <= t[i + 1]);
		}

		public OrderedLE(Problem pb, Variable[] scp, int[] lengths) {
			super(pb, scp, lengths);
		}

		public OrderedLE(Problem pb, Variable[] scp) {
			super(pb, scp);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			for (int i = scp.length - 2; i >= 0; i--)
				if (!scp[i].dom.removeValuesGT(scp[i + 1].dom.lastValue() - lengths[i]))
					return false;
			for (int i = 0; i < scp.length - 1; i++)
				if (!scp[i + 1].dom.removeValuesLT(scp[i].dom.firstValue() + lengths[i]))
					return false;
			return true;
		}
	}

	public static final class OrderedGE extends Ordered {

		@Override
		public final boolean checkValues(int[] t) {
			return IntStream.range(0, t.length - 1).allMatch(i -> t[i] + lengths[i] >= t[i + 1]);
		}

		public OrderedGE(Problem pb, Variable[] scp, int[] lengths) {
			super(pb, scp, lengths);
		}

		public OrderedGE(Problem pb, Variable[] scp) {
			super(pb, scp);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			for (int i = 0; i < scp.length - 1; i++)
				if (!scp[i + 1].dom.removeValuesGT(scp[i].dom.lastValue() + lengths[i]))
					return false;
			for (int i = scp.length - 2; i >= 0; i--)
				if (!scp[i].dom.removeValuesLT(scp[i + 1].dom.firstValue() - lengths[i]))
					return false;
			return true;
		}
	}

	public static final class OrderedGT extends Ordered {

		@Override
		public final boolean checkValues(int[] t) {
			return IntStream.range(0, t.length - 1).allMatch(i -> t[i] + lengths[i] > t[i + 1]);
		}

		public OrderedGT(Problem pb, Variable[] scp, int[] lengths) {
			super(pb, scp, lengths);
		}

		public OrderedGT(Problem pb, Variable[] scp) {
			super(pb, scp);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			for (int i = 0; i < scp.length - 1; i++)
				if (!scp[i + 1].dom.removeValuesGE(scp[i].dom.lastValue() + lengths[i]))
					return false;
			for (int i = scp.length - 2; i >= 0; i--)
				if (!scp[i].dom.removeValuesLE(scp[i + 1].dom.firstValue() - lengths[i]))
					return false;
			return true;
		}
	}
}
