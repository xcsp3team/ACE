/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package constraints.extension;

import java.util.Arrays;

import interfaces.Tags.TagNegative;
import problem.Problem;
import variables.Domain;
import variables.Variable;

public final class ExtensionSTR1NEG extends ExtensionSTR1 implements TagNegative {

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.nConflicts = Variable.litterals(scp).intArray();
	}

	protected int[][] nConflicts;

	public ExtensionSTR1NEG(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	@Override
	protected void beforeFiltering() {
		super.beforeFiltering();
		for (int i = futvars.limit; i >= 0; i--)
			Arrays.fill(nConflicts[futvars.dense[i]], 0);
	}

	@Override
	public boolean runPropagator(Variable evt) {
		int depth = problem.solver.depth();
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			if (isValid(tuple)) {
				for (int j = futvars.limit; j >= 0; j--) {
					int x = futvars.dense[j];
					int a = tuple[x];
					nConflicts[x][a]++;
				}
			} else
				set.removeAtPosition(i, depth);
		}
		long nValidTuples = Domain.nValidTuplesBoundedAtMaxValueFor(doms);
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			Domain dom = scp[x].dom;
			long limit = nValidTuples / dom.size();
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				if (nConflicts[x][a] != limit) {
					cnt--;
					cnts[x]--;
					ac[x][a] = true;
				}
			}
		}
		return updateDomains();
	}
}
