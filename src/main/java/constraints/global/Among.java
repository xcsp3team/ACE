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
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.CtrGlobal;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagSymmetric;
import problem.Problem;
import utility.Kit;
import utility.sets.SetSparse;
import variables.Variable;
import variables.domains.Domain;

public final class Among extends CtrGlobal implements TagSymmetric, TagGACGuaranteed, TagFilteringCompleteAtEachCall {
	private static final int SEARCH_THRESHOLD = 10;

	@Override
	public boolean checkValues(int[] t) {
		return IntStream.of(t).filter(v -> isPresentInValues(v)).count() == k;
	}

	private final int[] values;

	private final int k;

	private final SetSparse mixedVariables;

	private final boolean linearSearch;

	private boolean isPresentInValues(int value) {
		return linearSearch ? Kit.isPresent(value, values) : Arrays.binarySearch(values, value) >= 0;
	}

	public Among(Problem pb, Variable[] list, int[] values, int k) {
		super(pb, list);
		this.values = values;
		this.k = k;
		this.mixedVariables = new SetSparse(list.length);
		this.linearSearch = values.length < SEARCH_THRESHOLD;
		defineKey(Kit.join(values), k);
		control(Kit.isStrictlyIncreasing(values), "Values must be given in increasing order");
		control(0 < k && k < list.length, "Bad value of k=" + k);
		control(Stream.of(list).allMatch(x -> x.dom.size() > 1 && IntStream.of(values).anyMatch(v -> x.dom.isPresentValue(v))), "Badly formed scope.");
	}

	@Override
	public boolean runPropagator(Variable x) {
		int nGuaranteedVars = 0, nPossibleVars = 0;
		mixedVariables.clear();
		for (int i = 0; i < scp.length; i++) {
			Domain dom = scp[i].dom;
			boolean atLeastOnePresentValue = false, atLeastOneAbsentValue = false;
			for (int a = dom.first(); a != -1 && (!atLeastOnePresentValue || !atLeastOneAbsentValue); a = dom.next(a)) {
				boolean b = isPresentInValues(dom.toVal(a));
				atLeastOnePresentValue = atLeastOnePresentValue || b;
				atLeastOneAbsentValue = atLeastOneAbsentValue || !b;
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
			for (int i = mixedVariables.limit; i >= 0; i--) {
				Domain dom = scp[mixedVariables.dense[i]].dom;
				dom.removeIndexesChecking(a -> isPresentInValues(dom.toVal(a))); // no inconsistency possible
			}
			return true;
		}
		if (nPossibleVars < k)
			return x.dom.fail();
		if (nPossibleVars == k) {
			for (int i = mixedVariables.limit; i >= 0; i--) {
				Domain dom = scp[mixedVariables.dense[i]].dom;
				dom.removeIndexesChecking(a -> !isPresentInValues(dom.toVal(a))); // no inconsistency possible
			}
		}
		return true;
	}

}
