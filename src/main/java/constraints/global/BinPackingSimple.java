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
import java.util.stream.LongStream;

import constraints.CtrGlobal;
import interfaces.TagFilteringPartialAtEachCall;
import interfaces.TagGACUnguaranteed;
import problem.Problem;
import utility.Kit;
import utility.sets.SetDense;
import variables.Variable;
import variables.domains.Domain;

public final class BinPackingSimple extends CtrGlobal implements TagGACUnguaranteed, TagFilteringPartialAtEachCall {
	@Override
	public final boolean checkValues(int[] t) {
		Arrays.fill(sums, 0);
		for (int i = 0; i < t.length; i++)
			sums[scp[i].dom.toIdx(t[i])] += sizes[i];
		return LongStream.of(sums).noneMatch(l -> l > limit);
	}

	private final int[] sizes;
	private final int limit;

	private final long[] sums;

	private final SetDense set;

	public BinPackingSimple(Problem pb, Variable[] scp, int[] sizes, int limit) {
		super(pb, scp);
		Kit.control(scp.length >= 2 && Variable.haveSameDomainType(scp));
		defineKey(Kit.join(sizes) + " " + limit);
		this.sizes = sizes;
		this.limit = limit;
		this.sums = new long[scp[0].dom.initSize()];
		this.set = new SetDense(scp.length);
	}

	@Override
	public boolean runPropagator(Variable x) {
		Arrays.fill(sums, 0);
		set.clear();
		for (int i = 0; i < scp.length; i++) {
			int a = scp[i].dom.size() > 1 ? -1 : scp[i].dom.unique();
			if (a != -1)
				sums[a] += sizes[i];
			else
				set.add(i);
		}
		for (int i = 0; i < sums.length; i++)
			if (sums[i] > limit)
				return x.dom.fail();
		for (int i = set.limit; i >= 0; i--) {
			int p = set.dense[i];
			Domain dom = scp[p].dom;
			int sizeBefore = dom.size();
			for (int a = dom.first(); a != -1; a = dom.next(a))
				if (sums[a] + sizes[p] > limit)
					scp[p].dom.removeElementary(a);
			if (scp[p].dom.afterElementaryCalls(sizeBefore) == false)
				return false;
		}
		return true;
	}

}
