/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.Map;
import java.util.TreeMap;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import constraints.Constraint.CtrGlobal;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import sets.SetDense;
import sets.SetSparseReversible;
import variables.Domain;
import variables.Variable;

/**
 * This constraint ensures that all values assigned to the variables of its cope are all equal.
 */
public final class AllEqual extends CtrGlobal implements ObserverOnBacktracksSystematic, TagAC, TagFilteringCompleteAtEachCall, TagSymmetric {

	@Override
	public final boolean checkValues(int[] t) {
		for (int v : t)
			if (v != t[0])
				return false;
		return true;
	}

	@Override
	public void restoreBefore(int depth) {
		remainingValues.restoreLimitAtLevel(depth);
	}

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.remainingValues = new SetSparseReversible(map.size(), problem.variables.length + 1);
		this.lastRemovedValues = new SetDense(map.size());
	}

	private final Map<Integer, Integer> map; // keys are all possible variable values, and values are their indexes in the sparse set

	private SetSparseReversible remainingValues;

	private SetDense lastRemovedValues;

	public AllEqual(Problem pb, Variable[] list) {
		super(pb, list);
		int[] allValues = Variable.setOfvaluesIn(list).stream().mapToInt(v -> v).sorted().toArray();
		this.map = IntStream.range(0, allValues.length).boxed().collect(Collectors.toMap(i -> allValues[i], i -> i, (v1, v2) -> v1 + v2, TreeMap::new));
		control(list.length > 1 && allValues.length > 1);
		defineKey();
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (remainingValues.size() == 1) // only one remaining value, so entailed
			return true;

		Variable y = x.dom.size() == 1 ? x : Variable.firstSingletonVariableIn(scp); // we look for a variable y with a singleton domain

		if (y != null) { // we remove the unique value from the domains of the future variables
			int v = y.dom.singleValue();
			for (Variable z : scp)
				if (z != y && z.dom.reduceToValue(v) == false)
					return false;
			remainingValues.reduceTo(map.get(v), problem.solver.depth());
			return true;
		}

		// // we collect the set of dropped values (since the last call) over all future variables
		lastRemovedValues.clear();
		for (Domain dom : doms)
			for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a)) {
				int v = dom.toVal(a);
				if (!remainingValues.contains(map.get(v)))
					break;
				if (!lastRemovedValues.contains(v))
					lastRemovedValues.add(v);
			}
		if (lastRemovedValues.size() == remainingValues.size())
			return x.dom.fail();

		for (int i = scp.length - 1; i >= 0; i--) // for domino-5000, the reverse (0 to scp.length) is very slow. (due to revision ordering heuristic)
			scp[i].dom.removeValuesIn(lastRemovedValues); // no possible inconsistency at this level

		int depth = problem.solver.depth();
		for (int i = lastRemovedValues.limit; i >= 0; i--)
			remainingValues.remove(map.get(lastRemovedValues.dense[i]), depth);
		return true;
	}
}
