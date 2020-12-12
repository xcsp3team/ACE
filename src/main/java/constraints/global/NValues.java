/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint.CtrGlobal;
import interfaces.Tags.TagGACUnguaranteed;
import optimization.Optimizable;
import problem.Problem;
import sets.SetDense;
import variables.Domain;
import variables.Variable;
import variables.Variable.VariableInteger;

public abstract class NValues extends CtrGlobal implements TagGACUnguaranteed { // not call filtering-complete

	protected final Variable[] list;

	protected final Set<Integer> fixedVals;

	protected final SetDense unfixedVars; // unfixed variables with domains not in fixed vals (this is an approximation)

	protected final int[] sentinels;

	public NValues(Problem pb, Variable[] scp, Variable[] list) {
		super(pb, scp);
		this.list = list;
		this.fixedVals = new HashSet<>(Variable.setOfvaluesIn(list).size());
		this.unfixedVars = new SetDense(list.length);
		this.sentinels = new int[list.length];
	}

	protected void initializeSets() {
		fixedVals.clear();
		unfixedVars.clear();
		for (int i = 0; i < list.length; i++)
			if (list[i].dom.size() == 1)
				fixedVals.add(list[i].dom.firstValue());
			else
				unfixedVars.add(i);
		extern: for (int i = unfixedVars.limit; i >= 0; i--) {
			int x = unfixedVars.dense[i];
			Domain dom = list[x].dom;
			if (dom.size() > fixedVals.size())
				continue;
			int sentinel = sentinels[x];
			if (dom.isPresentValue(sentinel) && !fixedVals.contains(sentinel))
				continue;
			if (dom.size() > 5) // hard coding for avoiding iterating systematically over all values
				continue;
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int va = dom.toVal(a);
				if (!fixedVals.contains(va)) {
					sentinels[x] = va;
					continue extern;
				}
			}
			unfixedVars.removeAtPosition(i); // because all values in its domain correspond to fixed values
		}
	}

	/**********************************************************************************************
	 * NValuesCst
	 *********************************************************************************************/

	public static abstract class NValuesCst extends NValues implements Optimizable {

		protected long limit;

		@Override
		public long limit() {
			return limit;
		}

		@Override
		public void limit(long newLimit) {
			this.limit = newLimit;
			control(minComputableObjectiveValue() <= limit && limit <= maxComputableObjectiveValue());
		}

		@Override
		public long minComputableObjectiveValue() {
			return 1;
		}

		@Override
		public long maxComputableObjectiveValue() {
			return list.length;
		}

		public long minCurrentObjectiveValue() {
			throw new UnsupportedOperationException("not implemented"); // how to compute that?
		}

		public long maxCurrentObjectiveValue() {
			throw new UnsupportedOperationException("not implemented"); // how to compute that?
		}

		@Override
		public long objectiveValue() {
			return Arrays.stream(scp).mapToInt(x -> x.dom.uniqueValue()).distinct().count();
		}

		public NValuesCst(Problem pb, Variable[] list, long k) {
			super(pb, list, list);
			limit(k);
			defineKey(k);
		}

		public final static class NValuesCstLE extends NValuesCst {

			@Override
			public boolean checkValues(int[] t) {
				return Arrays.stream(t).distinct().count() <= limit;
			}

			public NValuesCstLE(Problem pb, Variable[] list, long k) {
				super(pb, list, Math.min(k, list.length));
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (x == null || x.dom.size() == 1) {
					initializeSets();
					if (fixedVals.size() > limit)
						return x == null ? false : x.dom.fail();
					if (fixedVals.size() == limit) {
						for (int i = unfixedVars.limit; i >= 0; i--)
							if (list[unfixedVars.dense[i]].dom.removeValuesNotIn(fixedVals) == false)
								return false;
						return entailed();
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

			public NValuesCstGE(Problem pb, Variable[] list, long k) {
				super(pb, list, Math.max(k, 1));
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (x == null || x.dom.size() == 1) {
					initializeSets();
					if (fixedVals.size() + unfixedVars.size() < limit)
						return x == null ? false : x.dom.fail();
					if (fixedVals.size() + unfixedVars.size() == limit) {
						for (int i = unfixedVars.limit; i >= 0; i--)
							if (list[unfixedVars.dense[i]].dom.removeValuesIn(fixedVals) == false)
								return false;
						if (unfixedVars.size() == 0)
							return entailed();
					}
				}
				return true;
			}
		}
	}

	/**********************************************************************************************
	 * NValuesVar
	 *********************************************************************************************/

	public static abstract class NValuesVar extends NValues {

		protected Variable k;

		public NValuesVar(Problem pb, Variable[] list, VariableInteger k) {
			super(pb, pb.vars(list, k), list);
			control(Stream.of(list).noneMatch(x -> x == k), "currently, k must not be present in the list");
			this.k = k;
		}

		public static class NValuesVarEQ extends NValuesVar {

			@Override
			public boolean checkValues(int[] t) {
				return IntStream.range(0, t.length - 1).map(i -> t[i]).distinct().count() == t[t.length - 1];
			}

			public NValuesVarEQ(Problem pb, Variable[] list, VariableInteger k) {
				super(pb, list, k);
			}

			@Override
			public boolean runPropagator(Variable x) {
				if (x.dom.size() == 1) {
					initializeSets();
					if (k.dom.removeValuesLT(fixedVals.size()) == false || k.dom.removeValuesGT(fixedVals.size() + unfixedVars.size()) == false)
						return false;
					if (k.dom.size() == 1) {
						int limit = k.dom.uniqueValue();
						if (fixedVals.size() == limit) {
							for (int i = unfixedVars.limit; i >= 0; i--)
								if (list[unfixedVars.dense[i]].dom.removeValuesNotIn(fixedVals) == false)
									return false;
							return entailed();
						} else if (fixedVals.size() + unfixedVars.size() == limit) {
							for (int i = unfixedVars.limit; i >= 0; i--)
								if (list[unfixedVars.dense[i]].dom.removeValuesIn(fixedVals) == false)
									return false;
						}
					}
				}
				return true;
			}
		}
	}
}
