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
import problem.Problem;
import utility.Kit;
import utility.sets.SetDenseReversible;
import variables.Variable;

public class CtrExtensionSTR1 extends CtrExtensionGlobal {

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		this.tuples = ((Table) extStructure).tuples;
		this.set = new SetDenseReversible(tuples.length, pb.variables.length + 1);
		Kit.control(tuples.length > 0);
	}

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
	}

	protected int[][] tuples; // redundant field (reference to tuples in Table)

	public SetDenseReversible set; // storing the indexes of the current table

	/**
	 * ac[x][a] indicates if a support has been found for (x,a)
	 */
	protected boolean[][] ac;

	/**
	 * cnts[x] is the number of values in the current domain of x with no found support (yet)
	 */
	protected int[] cnts;

	/**
	 * The total number of values over all variables in the scope of this constraint with no found support (yet)
	 */
	protected int cnt;

	public CtrExtensionSTR1(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length > 1, "Arity must be at least 2");
	}

	@Override
	protected ExtensionStructureHard buildExtensionStructure() {
		return new Table(this);
	}

	protected final void buildBasicCollectingStructures() {
		this.ac = Variable.litterals(scp).booleanArray();
		this.cnts = new int[scp.length];
	}

	@Override
	protected void initSpecificStructures() {
		buildBasicCollectingStructures();
	}

	protected void beforeFiltering() {
		cnt = 0;
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			cnt += (cnts[x] = doms[x].size());
			Arrays.fill(ac[x], false);
		}
	}

	protected boolean updateDomains() {
		for (int i = futvars.limit; i >= 0 && cnt > 0; i--) {
			int x = futvars.dense[i];
			int nRemovals = cnts[x];
			if (nRemovals == 0)
				continue;
			if (doms[x].remove(ac[x], nRemovals) == false)
				return false;
			cnt -= nRemovals;
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		// pb.stuff.updateStatsForSTR(set);
		int depth = pb.solver.depth();
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			if (isValid(tuple)) {
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
