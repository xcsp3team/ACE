/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension;

import constraints.hard.extension.structures.ExtensionStructureHard;
import constraints.hard.extension.structures.TableCompressed3;
import interfaces.TagExperimental;
import problem.Problem;
import variables.Variable;

public class CtrExtensionSTRCPRS extends CtrExtensionSTR1 implements TagExperimental {

	protected TableCompressed3 tableCompressed;

	protected int[][] stamps; // 1D = pattern id ; 2D = position ; value = stamp

	private int time = 1;

	public CtrExtensionSTRCPRS(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	@Override
	protected ExtensionStructureHard buildExtensionStructure() {
		return new TableCompressed3(this);
	}

	@Override
	protected void initSpecificStructures() {
		super.initSpecificStructures();
		tableCompressed = (TableCompressed3) extStructure;
		stamps = new int[tableCompressed.patterns.length][scp.length];
	}

	@Override
	protected void beforeFiltering() {
		time++;
		super.beforeFiltering();
	}

	public final boolean checkValidityOfCompressedTuple(int[] tuple) {
		for (int vap = 0, gap = 0; vap < tuple.length; vap++) {
			int posnc = vap + gap;
			int val = tuple[vap];
			if (val >= 0) {
				if (!doms[posnc].isPresent(val))
					return false;
			} else {
				int[] patternStamps = stamps[-val];
				if (patternStamps[posnc] == -time) {
					return false;
				}
				int[] pattern = tableCompressed.patterns[-val];
				if (patternStamps[posnc] != time) {
					for (int i = pattern.length - 1; i >= 0; i--)
						if (!doms[posnc + i].isPresent(pattern[i])) {
							patternStamps[posnc] = -time;
							return false;
						}
					patternStamps[posnc] = time;
				}
				gap += pattern.length - 1;
			}
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		pb.stuff.updateStatsForSTR(set);
		int depth = pb.solver.depth();
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			int[] compressedTuple = tableCompressed.tuples[set.dense[i]];
			if (checkValidityOfCompressedTuple(compressedTuple)) {
				int[] tuple = tableCompressed.decompress(compressedTuple);
				for (int j = futvars.limit; j >= 0; j--) {
					int x = futvars.dense[j];
					int a = tuple[x];
					if (!ac[x][a]) {
						cnt--;
						cnts[x]--;
						ac[x][a] = true;
					}
				}
			} else
				set.removeAtPosition(i, depth);
		}
		return updateDomains();
	}

}
