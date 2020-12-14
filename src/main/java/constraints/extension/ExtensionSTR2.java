/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension;

import static org.xcsp.common.Constants.STAR;

import java.util.stream.Stream;

import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import interfaces.Tags.TagShort;
import problem.Problem;
import utility.Kit;
import variables.Variable;

// why not using a counter 'time' and replace boolean[][] ac by int[][] ac (we just do time++ instead of Arrays.fill(ac[x],false)
public class ExtensionSTR2 extends ExtensionSTR1Optimized implements TagShort {

	boolean isShort;

	public ExtensionSTR2(Problem pb, Variable... scp) {
		super(pb, scp);
	}

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		Table table = new Table(this);
		this.isShort = table.isShort;
		return table;
	}

	protected boolean isValidTuple(int[] tuple) {
		for (int i = sValSize - 1; i >= 0; i--) {
			int x = sVal[i];
			if (tuple[x] != STAR && !doms[x].present(tuple[x]))
				return false;
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
		// if (!isShort && Variable.nValidTuplesBoundedAtMaxValueFor(scp) == set.size()) {
		// // assert
		// // System.out.println("entailed " + set.size() + " " + futvars.size());
		// return entailed();
		// }
		return updateDomains();
	}

	private boolean controlValidTuples() {
		int[] dense = set.dense;
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[dense[i]];
			for (int j = tuple.length - 1; j >= 0; j--) {
				if (tuple[j] != STAR && !doms[j].present(tuple[j])) {
					System.out.println(this + " at " + problem.solver.depth() + "\n" + Kit.join(tuple));
					Stream.of(scp).forEach(x -> x.display(true));
					return false;
				}
			}
		}
		return true;
	}

}
