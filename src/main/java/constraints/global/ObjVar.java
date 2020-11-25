/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import constraints.Constraint.CtrGlobal;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagSymmetric;
import optimization.Optimizable;
import problem.Problem;
import variables.Variable;

public abstract class ObjVar extends CtrGlobal implements Optimizable, TagFilteringCompleteAtEachCall, TagSymmetric, TagGACGuaranteed {

	@Override
	public long minComputableObjectiveValue() {
		return x.dom.toVal(0);
	}

	@Override
	public long maxComputableObjectiveValue() {
		return x.dom.toVal(x.dom.initSize() - 1);
	}

	@Override
	public long minCurrentObjectiveValue() {
		return x.dom.firstValue();
	}

	@Override
	public long maxCurrentObjectiveValue() {
		return x.dom.lastValue();
	}

	@Override
	public long limit() {
		return limit;
	}

	@Override
	public final void limit(long newLimit) {
		this.limit = newLimit;
		entailed = false;
		control(minComputableObjectiveValue() <= limit && limit <= maxComputableObjectiveValue());
	}

	@Override
	public long objectiveValue() {
		return x.dom.uniqueValue();
	}

	protected Variable x;

	protected long limit;

	protected boolean entailed;

	public ObjVar(Problem pb, Variable x, long limit) {
		super(pb, new Variable[] { x });
		this.x = x;
		limit(limit);
	}

	public static final class ObjVarLE extends ObjVar {

		@Override
		public boolean checkValues(int[] vals) {
			return vals[0] <= limit;
		}

		public ObjVarLE(Problem pb, Variable x, long limit) {
			super(pb, x, Math.min(limit, x.dom.lastValue()));
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
			super(pb, x, Math.max(limit, x.dom.firstValue()));
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
