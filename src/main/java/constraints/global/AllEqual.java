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

import static java.util.stream.Collectors.toMap;
import static utility.Kit.control;

import java.util.Map;
import java.util.TreeMap;
import java.util.stream.IntStream;

import constraints.ConstraintGlobal;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import sets.SetDense;
import sets.SetSparseReversible;
import variables.Domain;
import variables.Variable;

/**
 * This constraint AllEqual ensures that all values assigned to the variables of its scope are all equal. It is
 * essentially an ease of modeling for the user (because it can be trivially decomposed into binary equality
 * constraints).
 * 
 * @author Christophe Lecoutre
 */
public final class AllEqual extends ConstraintGlobal implements TagAC, TagCallCompleteFiltering, TagSymmetric, ObserverOnBacktracksSystematic {

	/**********************************************************************************************
	 * Implementing interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction(int n) {
		super.afterProblemConstruction(n);
		this.remainingValues = new SetSparseReversible(map.size(), n + 1);
	}

	@Override
	public void restoreBefore(int depth) {
		remainingValues.restoreLimitAtLevel(depth);
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	@Override
	public final boolean isSatisfiedBy(int[] t) {
		for (int v : t)
			if (v != t[0])
				return false;
		return true;
	}

	/**
	 * A reversible sparse set containing the values that can be used, at a given time, to satisfy the constraint
	 */
	private SetSparseReversible remainingValues;

	/**
	 * a map such that keys are all possible values (from variable domains), and values are their indexes in the
	 * reversible sparse set
	 */
	private final Map<Integer, Integer> map;

	/**
	 * A set used temporarily when filtering
	 */
	private final SetDense lastRemoved;

	/**
	 * Build a constraint AllEqual for the specified problem over the specified array/list of variables
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public AllEqual(Problem pb, Variable[] scp) {
		super(pb, scp);
		int[] values = Variable.setOfvaluesIn(scp).stream().mapToInt(v -> v).sorted().toArray();
		this.map = IntStream.range(0, values.length).boxed().collect(toMap(i -> values[i], i -> i, (v1, v2) -> v1 + v2, TreeMap::new)); // useless merger
		this.lastRemoved = new SetDense(map.size());
		control(scp.length > 1 && values.length >= 1);
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (remainingValues.size() == 1) // only one remaining value, so entailed
			return entailed();

		// we look for a variable with a singleton domain
		Variable y = x.dom.size() == 1 ? x : Variable.firstSingletonVariableIn(scp);

		if (y != null) { // we remove the unique value from the domains of the future variables
			int v = y.dom.singleValue();
			for (Variable z : scp)
				if (z != y && z.dom.reduceToValue(v) == false)
					return false;
			remainingValues.reduceTo(map.get(v), problem.solver.depth());
			return entailed();
		}
		// we collect the set of removed values (since the last call) over all future variables
		lastRemoved.clear();
		for (Domain dom : doms)
			for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a)) {
				int v = dom.toVal(a);
				if (!remainingValues.contains(map.get(v)))
					break;
				if (!lastRemoved.contains(v))
					lastRemoved.add(v);
			}
		if (lastRemoved.size() == remainingValues.size())
			return x.dom.fail();
		for (int i = scp.length - 1; i >= 0; i--)
			// for domino-5000, the reverse (0 to scp.length) is very slow. (due to revision ordering heuristic)
			doms[i].removeValuesIn(lastRemoved); // no possible inconsistency at this level
		int depth = problem.solver.depth();
		for (int i = lastRemoved.limit; i >= 0; i--)
			remainingValues.remove(map.get(lastRemoved.dense[i]), depth);
		return true;
	}
}
