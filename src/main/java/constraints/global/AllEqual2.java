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
import interfaces.Observers.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import sets.SetDense;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This constraint ensures that all values assigned to the variables of its cope are all equal.
 */
public final class AllEqual2 extends CtrGlobal implements ObserverBacktrackingSystematic, TagGACGuaranteed, TagFilteringCompleteAtEachCall, TagSymmetric {

	@Override
	public final boolean checkValues(int[] t) {
		return IntStream.range(0, t.length - 1).allMatch(i -> t[i] == t[i + 1]);
	}

	@Override
	public void restoreBefore(int depth) {
		remainingValues.restoreLimitAtLevel(depth);
	}

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.remainingValues = new SetSparseReversible(map.size(), pb.variables.length + 1);
		this.lastRemovedValues = new SetDense(map.size());
	}

	private final Map<Integer, Integer> map; // keys are all possible variable values, and values are their indexes in the sparse set

	private SetSparseReversible remainingValues;

	private SetDense lastRemovedValues;

	public AllEqual2(Problem pb, Variable[] list) {
		super(pb, list);
		int[] allValues = Variable.setOfvaluesIn(list).stream().mapToInt(v -> v).sorted().toArray();
		this.map = IntStream.range(0, allValues.length).boxed().collect(Collectors.toMap(i -> allValues[i], i -> i, (v1, v2) -> v1 + v2, TreeMap::new));
		Kit.control(allValues.length > 1 && list.length >= 2);
		defineKey();
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (remainingValues.size() == 1) // only one remaining value, so entailed
			return true;
		Variable y = x.dom.size() == 1 ? x : null;
		if (y == null)
			for (Variable z : scp)
				if (z.dom.size() == 1) {
					y = z;
					break;
				}
		if (y != null) { // we remove the unique value from the domains of the future variables
			int v = y.dom.uniqueValue();
			for (Variable z : scp)
				if (z != y && z.dom.reduceToValue(v) == false)
					return false;
			remainingValues.reduceTo(map.get(v), pb.solver.depth());
			return true;
		}
		lastRemovedValues.clear();
		for (Domain dom : doms) {
			for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a)) {
				int v = dom.toVal(a);
				if (!remainingValues.isPresent(map.get(v)))
					break;
				lastRemovedValues.add(v);
			}
		}
		if (lastRemovedValues.size() == remainingValues.size())
			return x.dom.fail();

		for (int j = scp.length - 1; j >= 0; j--) // for domino, the reverse (0 to scp.length) is very slow. why? (question of cache ?)
			scp[j].dom.removeValuesIn(lastRemovedValues); // no possible inconsistency at this level

		int depth = pb.solver.depth();
		for (int i = lastRemovedValues.limit; i >= 0; i--)
			remainingValues.remove(map.get(lastRemovedValues.dense[i]), depth);
		return true;
	}
}

// for (Domain dom : doms)
// dom.removeValuesIn(lastRemovedValues);

// for (int i = lastRemovedValues.limit; i >= 0; i--) {
// int v = lastRemovedValues.dense[i];
// for (int j = scp.length - 1; j >= 0; j--) // for domino, the reverse (0 to scp.length) is very slow. why? (question of cache ?)
// scp[j].dom.removeValue(v, false); // no possible inconsistency at this level
// remainingValues.remove(map.get(v), depth);
// }