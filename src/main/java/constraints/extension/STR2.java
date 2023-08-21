/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension;

import static org.xcsp.common.Constants.STAR;

import java.util.stream.Stream;

import interfaces.Tags.TagStarredCompatible;
import problem.Problem;
import utility.Kit;
import variables.Variable;

/**
 * This is STR2 (Simple Tabular Reduction, v2), for filtering extension (table) constraints, as described in: <br />
 * Christophe Lecoutre: STR2: optimized simple tabular reduction for table constraints. Constraints An Int. J. 16(4): 341-371 (2011) <br />
 * This implementation can deal with starred tables.
 * 
 * @author Christophe Lecoutre
 */
public final class STR2 extends STR1Optimized implements TagStarredCompatible {

	/**
	 * Builds an extension constraint, with STR2 as specific filtering method
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public STR2(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	private boolean isValidTuple(int[] tuple) {
		for (int i = sValSize - 1; i >= 0; i--) {
			int x = sVal[i];
			if (tuple[x] != STAR && !doms[x].contains(tuple[x]))
				return false;
		}
		return true;
	}

	private boolean controlValidTuples() {
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			for (int j = tuple.length - 1; j >= 0; j--)
				if (tuple[j] != STAR && !doms[j].contains(tuple[j])) {
					System.out.println(this + " at " + problem.solver.depth() + "\n" + Kit.join(tuple));
					Stream.of(scp).forEach(x -> x.display(2));
					return false;
				}
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		int depth = problem.solver.depth();
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			if (isValidTuple(tuple)) {
				for (int j = sSupSize - 1; j >= 0; j--) {
					int x = sSup[j];
					int a = tuple[x];
					if (a == STAR) {
						cnts[x] = 0;
						sSup[j] = sSup[--sSupSize];
					} else if (!ac[x][a]) {
						ac[x][a] = true;
						if (--cnts[x] == 0)
							sSup[j] = sSup[--sSupSize];
					}
				}
			} else
				set.removeAtPosition(i, depth);
		}
		assert controlValidTuples();
		// if (!table.starred && Variable.nValidTuplesBoundedAtMaxValueFor(scp) == set.size()) return entailed();
		return updateDomains();
	}
}
