/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import static java.util.stream.Collectors.toCollection;
import static utility.Kit.control;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * The constraint Among is a special case of the constraint Count, with a set of values as target (contrary to classes
 * that you can find in the Java class global.Count).
 * 
 * @author Christophe Lecoutre
 */
public final class Among extends ConstraintGlobal implements TagAC, TagCallCompleteFiltering, TagSymmetric {

	@Override
	public boolean isSatisfiedBy(int[] t) {
		int cnt = 0;
		for (int v : t)
			if (values.contains(v))
				cnt++;
		return cnt == k;
	}

	/**
	 * The values that must be counted (in those assigned to the variables of the scope of the constraint)
	 */
	private final Set<Integer> values;

	/**
	 * The limit (number of occurrences) to reach
	 */
	private final int k;

	/**
	 * A set used temporarily when filtering
	 */
	private final SetSparse mixedVariables;

	/**
	 * Builds a constraint Among for the specified problem
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param list
	 *            the list of variables where we have to count
	 * @param values
	 *            the values that we consider when counting
	 * @param k
	 *            the number of occurrences to reach
	 */
	public Among(Problem pb, Variable[] list, int[] values, int k) {
		super(pb, list);
		control(values.length > 1 && Kit.isStrictlyIncreasing(values), "Values must be given in increasing order");
		control(0 < k && k < list.length, "Bad value of k=" + k);
		control(Stream.of(list).allMatch(x -> x.dom.size() > 1 && IntStream.of(values).anyMatch(v -> x.dom.containsValue(v))), "Badly formed scope");
		this.values = IntStream.of(values).boxed().collect(toCollection(LinkedHashSet::new)); // TODO HashSet better than TreeSet?
		this.k = k;
		this.mixedVariables = new SetSparse(list.length);
		defineKey(values, k);
	}

	@Override
	public boolean runPropagator(Variable x) {
		int nGuaranteedVars = 0, nPossibleVars = 0;
		mixedVariables.clear();
		for (int i = 0; i < scp.length; i++) {
			Domain dom = scp[i].dom;
			boolean atLeastOnePresentValue = false, atLeastOneAbsentValue = false;
			for (int a = dom.first(); a != -1 && (!atLeastOnePresentValue || !atLeastOneAbsentValue); a = dom.next(a)) {
				boolean among = values.contains(dom.toVal(a));
				atLeastOnePresentValue = atLeastOnePresentValue || among;
				atLeastOneAbsentValue = atLeastOneAbsentValue || !among;
			}
			if (atLeastOnePresentValue) {
				nPossibleVars++;
				if (!atLeastOneAbsentValue && ++nGuaranteedVars > k)
					return dom.fail(); // inconsistency detected
				if (atLeastOneAbsentValue)
					mixedVariables.add(i);
			}
		}
		if (nGuaranteedVars == k) {
			for (int i = mixedVariables.limit; i >= 0; i--)
				scp[mixedVariables.dense[i]].dom.removeValuesIn(values); // no inconsistency possible
			return entail();
		}
		if (nPossibleVars < k)
			return x.dom.fail();
		if (nPossibleVars == k) {
			for (int i = mixedVariables.limit; i >= 0; i--)
				scp[mixedVariables.dense[i]].dom.removeValuesNotIn(values); // no inconsistency possible
			return entail();
		}
		return true;
	}

}
