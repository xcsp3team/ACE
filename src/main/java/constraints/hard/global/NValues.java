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

import org.xcsp.common.Types.TypeConditionOperatorSet;
import org.xcsp.modeler.definitions.DefXCSP;

import interfaces.OptimizationCompatible;
import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public abstract class NValues extends NValuesAbstract implements OptimizationCompatible {

	protected int limit;

	@Override
	public long minComputableObjectiveValue() {
		return 1;
	}

	@Override
	public long maxComputableObjectiveValue() {
		return list.length;
	}

	@Override
	public long getLimit() {
		return limit;
	}

	@Override
	public void setLimit(long newLimit) {
		Kit.control(Integer.MIN_VALUE <= newLimit && newLimit <= Integer.MAX_VALUE);
		// Kit.control(newLimit < limit, () -> newLimit + " replacing " + limit);
		limit = (int) newLimit;
	}

	@Override
	public long objectiveValue() {
		return Arrays.stream(scp).mapToInt(x -> x.dom.uniqueValue()).distinct().count();
	}

	public NValues(Problem pb, Variable[] list, int k) {
		super(pb, list, list);
		Kit.control(1 <= k && k <= list.length);
		this.limit = k;
		defineKey(k);
	}

	@Override
	public DefXCSP defXCSP() {
		String operator = this instanceof NValuesLE ? "le" : "ge";
		return new DefXCSP(NVALUES).addSon(LIST, compact(list)).addSon(CONDITION, "(" + operator + "," + limit + ")");
	}

	public final static class NValuesLE extends NValues {

		@Override
		public boolean checkValues(int[] t) {
			return Arrays.stream(t).distinct().count() <= limit;
		}

		public NValuesLE(Problem pb, Variable[] list, int k) {
			super(pb, list, k);
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (x.dom.size() == 1) {
				fixedVals.clear();
				unfixedVars.clear();
				for (int i = 0; i < list.length; i++)
					if (list[i].dom.size() == 1)
						fixedVals.add(list[i].dom.firstValue());
					else
						unfixedVars.add(i);
				if (fixedVals.size() > limit)
					return x.dom.fail();
				if (fixedVals.size() == limit)
					for (int i = unfixedVars.limit; i >= 0; i--) {
						Domain dom = list[unfixedVars.dense[i]].dom;
						if (dom.removeValues(TypeConditionOperatorSet.NOTIN, fixedVals) == false)
							return false;
					}
			}
			return true;
		}
	}

	public final static class NValuesGE extends NValues {

		@Override
		public boolean checkValues(int[] t) {
			return Arrays.stream(t).distinct().count() >= limit;
		}

		public NValuesGE(Problem pb, Variable[] list, int k) {
			super(pb, list, k);
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (x.dom.size() == 1) {
				initializeSets();
				// fixedVals.clear();
				// unfixedVars.clear();
				// for (int i = 0; i < scp.length; i++)
				// if (scp[i].dom.size() == 1)
				// fixedVals.add(scp[i].dom.firstValue());
				// else
				// unfixedVars.add(i);
				if (fixedVals.size() + unfixedVars.size() < limit)
					return x.dom.fail();
				if (fixedVals.size() + unfixedVars.size() == limit)
					for (int i = unfixedVars.limit; i >= 0; i--) {
						Domain dom = list[unfixedVars.dense[i]].dom;
						if (dom.removeValues(TypeConditionOperatorSet.IN, fixedVals) == false)
							return false;
					}
			}
			return true;
		}
	}
}
