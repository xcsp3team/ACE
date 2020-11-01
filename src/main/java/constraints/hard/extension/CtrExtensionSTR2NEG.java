/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension;

import java.util.Arrays;

import constraints.hard.CtrExtension.CtrExtensionGlobal;
import constraints.hard.extension.structures.ExtensionStructureHard;
import constraints.hard.extension.structures.Table;
import interfaces.TagNegative;
import problem.Problem;
import utility.sets.SetDenseReversible;
import variables.Variable;

public class CtrExtensionSTR2NEG extends CtrExtensionGlobal implements TagNegative {

	/**********************************************************************************************
	 * Interfaces
	 *********************************************************************************************/

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
		Arrays.fill(nMaxConflicts, 0);
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	protected int[][] tuples; // redundant field (reference to tuples in Table)

	protected SetDenseReversible set;

	protected int[][] nConflicts; // nConflicts[x][a] indicates the number of conflicts in the current table for (x,a)

	protected int[] nMaxConflicts; // nMaxConflicts[x] indicates the maximum number of conflicts in the current table for a value of x

	protected long[] nValidTuples; // 1D = variable position

	protected int sSupSize;
	protected int[] sSup;

	public CtrExtensionSTR2NEG(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		this.tuples = ((Table) extStructure).tuples;
		this.set = new SetDenseReversible(tuples.length, pb.variables.length + 1);
		this.nConflicts = Variable.litterals(scp).intArray();
		this.nMaxConflicts = new int[scp.length];
		this.nValidTuples = new long[scp.length];
		this.sSup = new int[scp.length];
	}

	@Override
	protected ExtensionStructureHard buildExtensionStructure() {
		return new Table(this);
	}

	protected void initializeStructuresBeforeFiltering() {
		sSupSize = 0;
		long nValid = Variable.nValidTuplesBoundedAtMaxValueFor(scp);
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			long limit = nValid / doms[x].size();
			if (set.size() >= limit && set.size() >= nMaxConflicts[x]) {
				sSup[sSupSize++] = x;
				Arrays.fill(nConflicts[x], 0);
				nMaxConflicts[x] = 0;
				nValidTuples[x] = limit;
			}
		}
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		pb.stuff.updateStatsForSTR(set);
		int depth = pb.solver.depth();
		initializeStructuresBeforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			if (isValid(tuple)) {
				for (int j = sSupSize - 1; j >= 0; j--) {
					int x = sSup[j];
					int a = tuple[x];
					nMaxConflicts[x] = Math.max(nMaxConflicts[x], ++nConflicts[x][a]);
					if (nConflicts[x][a] == nValidTuples[x]) {
						if (scp[x].dom.remove(a) == false)
							return false;
					} else if (nMaxConflicts[x] + i < nValidTuples[x])
						sSup[j] = sSup[--sSupSize];
				}
			} else
				set.removeAtPosition(i, depth);
		}
		return true;
	}
}
