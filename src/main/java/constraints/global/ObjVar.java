/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.stream.Stream;

import constraints.CtrGlobal;
import interfaces.Optimizable;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagSymmetric;
import problem.Problem;
import variables.Variable;

public abstract class ObjVar extends CtrGlobal implements Optimizable, TagFilteringCompleteAtEachCall, TagSymmetric, TagGACGuaranteed {

	@Override
	public long minComputableObjectiveValue() {
		return Stream.of(scp).mapToLong(x -> x.dom.toVal(0)).min().getAsLong();
		// No problem to use a stream because only called once at construction time
	}

	@Override
	public long maxComputableObjectiveValue() {
		return Stream.of(scp).mapToLong(x -> x.dom.toVal(x.dom.initSize() - 1)).max().getAsLong();
		// No problem to use a stream because only called once at construction time
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

	@Override
	public long objectiveValue() {
		return x.dom.uniqueValue();
	}

	protected Variable x;

	protected int limit;

	protected boolean entailed;

	public ObjVar(Problem pb, Variable x, long limit) {
		super(pb, new Variable[] { x });
		this.x = x;
		this.limit = Math.toIntExact(limit);
	}

	public static final class ObjVarLE extends ObjVar {

		@Override
		public boolean checkValues(int[] vals) {
			return vals[0] <= limit;
		}

		public ObjVarLE(Problem pb, Variable x, long limit) {
			super(pb, x, limit);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (entailed)
				return true;
			control(pb.solver.depth() == 0);
			if (x.dom.removeValuesGT(limit) == false)
				return false;
			entailed = true;
			assert x.dom.size() > 0;
			return true;
		}
	}

	public static final class ObjVarGE extends ObjVar {

		@Override
		public boolean checkValues(int[] vals) {
			return vals[0] >= limit;
		}

		public ObjVarGE(Problem pb, Variable x, long limit) {
			super(pb, x, limit);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (entailed)
				return true;
			control(pb.solver.depth() == 0);
			if (x.dom.removeValuesLT(limit) == false)
				return false;
			entailed = true;
			assert x.dom.size() > 0;
			return true;
		}
	}
}
