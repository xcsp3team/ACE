/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import java.util.Arrays;

import interfaces.OptimizationCompatible;
import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public abstract class NValuesCst extends NValuesAbstract implements OptimizationCompatible {

	protected int limit;

	@Override
	public long getLimit() {
		return limit;
	}

	@Override
	public void setLimit(long newLimit) {
		limit = Math.toIntExact(newLimit);
	}

	@Override
	public long minComputableObjectiveValue() {
		return 1;
	}

	@Override
	public long maxComputableObjectiveValue() {
		return list.length;
	}

	@Override
	public long objectiveValue() {
		return Arrays.stream(scp).mapToInt(x -> x.dom.uniqueValue()).distinct().count();
	}

	public NValuesCst(Problem pb, Variable[] list, int k) {
		super(pb, list, list);
		Kit.control(1 <= k && k <= list.length);
		this.limit = k;
		defineKey(k);
	}

	public final static class NValuesCstLE extends NValuesCst {

		@Override
		public boolean checkValues(int[] t) {
			return Arrays.stream(t).distinct().count() <= limit;
		}

		public NValuesCstLE(Problem pb, Variable[] list, int k) {
			super(pb, list, k);
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (x == null || x.dom.size() == 1) {
				fixedVals.clear();
				unfixedVars.clear();
				for (int i = 0; i < list.length; i++)
					if (list[i].dom.size() == 1)
						fixedVals.add(list[i].dom.firstValue());
					else
						unfixedVars.add(i);
				if (fixedVals.size() > limit)
					return x == null ? false : x.dom.fail();
				if (fixedVals.size() == limit)
					for (int i = unfixedVars.limit; i >= 0; i--) {
						Domain dom = list[unfixedVars.dense[i]].dom;
						if (dom.removeValuesNotIn(fixedVals) == false)
							return false;
					}
			}
			return true;
		}
	}

	public final static class NValuesCstGE extends NValuesCst {

		@Override
		public boolean checkValues(int[] t) {
			return Arrays.stream(t).distinct().count() >= limit;
		}

		public NValuesCstGE(Problem pb, Variable[] list, int k) {
			super(pb, list, k);
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (x == null || x.dom.size() == 1) {
				initializeSets();
				// fixedVals.clear();
				// unfixedVars.clear();
				// for (int i = 0; i < scp.length; i++)
				// if (scp[i].dom.size() == 1)
				// fixedVals.add(scp[i].dom.firstValue());
				// else
				// unfixedVars.add(i);
				if (fixedVals.size() + unfixedVars.size() < limit)
					return x == null ? false : x.dom.fail();
				if (fixedVals.size() + unfixedVars.size() == limit)
					for (int i = unfixedVars.limit; i >= 0; i--) {
						Domain dom = list[unfixedVars.dense[i]].dom;
						if (dom.removeValuesIn(fixedVals) == false)
							return false;
					}
			}
			return true;
		}
	}
}
