/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension;

import java.util.Arrays;

import problem.Problem;
import propagation.order1.StrongConsistency;
import utility.Kit;
import variables.Variable;

public abstract class ExtensionSTROptimized extends ExtensionSTR1 {

	/**********************************************************************************************
	 * Interfaces
	 *********************************************************************************************/

	private final static int UNITIALIZED = -2;

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		this.sVal = new int[scp.length];
		this.sSup = new int[scp.length];
		if (decremental) {
			this.lastSizesStack = new int[pb.variables.length + 1][scp.length];
			Arrays.fill(lastSizesStack[0], UNITIALIZED);
		} else
			this.lastSizes = Kit.repeat(UNITIALIZED, scp.length);
	}

	@Override
	public void restoreBefore(int depth) {
		super.restoreBefore(depth);
		if (decremental)
			lastDepth = Math.max(0, Math.min(lastDepth, depth - 1));
		else
			Arrays.fill(lastSizes, UNITIALIZED);
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	protected boolean decremental; // true if we exploit decrementality

	protected int sValSize;
	protected int[] sVal; // positions of the variables for which validity must be checked

	protected int sSupSize;
	protected int[] sSup; // positions of the (future) variables for which some values still must be checked to be AC

	protected long lastCallLimit;

	protected int[] lastSizes; // lastSizes[x] is the domain size of x at the last call
	protected int[][] lastSizesStack; // lastSizesStack[i][x] is the domain size of x at the last call at level i
	protected int lastDepth; // the depth at the last call

	/**********************************************************************************************
	 * Method
	 *********************************************************************************************/

	public ExtensionSTROptimized(Problem pb, Variable[] scp) {
		super(pb, scp);
		this.decremental = pb.rs.cp.settingExtension.decremental;
	}

	protected void initRestorationStructuresBeforeFiltering() {
		if (decremental) {
			int depth = pb.solver.depth();
			assert 0 <= lastDepth && lastDepth <= depth : depth + " " + lastDepth + " " + this;
			for (int i = lastDepth + 1; i <= depth; i++)
				System.arraycopy(lastSizesStack[lastDepth], 0, lastSizesStack[i], 0, scp.length);
			lastSizes = lastSizesStack[depth];
			lastDepth = depth;
		}
	}

	protected void manageLastPastVar() {
		if (lastCallLimit != pb.solver.stats.nAssignments || pb.solver.propagation instanceof StrongConsistency) { // second condition due to Inverse4
			lastCallLimit = pb.solver.stats.nAssignments;
			Variable lastPast = pb.solver.futVars.lastPast();
			int x = lastPast == null ? -1 : positionOf(lastPast);
			if (x != -1) {
				sVal[sValSize++] = x;
				lastSizes[x] = 1;
			}
		}
	}

	@Override
	protected void beforeFiltering() {
		initRestorationStructuresBeforeFiltering();
		sValSize = sSupSize = 0;
		manageLastPastVar();
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			int domSize = doms[x].size();
			cnts[x] = domSize;
			if (lastSizes[x] != domSize) {
				sVal[sValSize++] = x;
				lastSizes[x] = domSize;
			}
			sSup[sSupSize++] = x;
			Arrays.fill(ac[x], false);
		}

		// TODO to experiment the code below
		// if (sValSize == 1) { int x = sVal[0]; for (int i = 0; i < sSupSize; i++) if (sSup[i] == x) { sSup[i] = sSup[--sSupSize]; break; } }
	}

	@Override
	protected boolean updateDomains() {
		for (int i = sSupSize - 1; i >= 0; i--) {
			int x = sSup[i];
			int nRemovals = cnts[x];
			assert nRemovals > 0;
			if (doms[x].remove(ac[x], nRemovals) == false)
				return false;
			lastSizes[x] = doms[x].size();
		}
		return true;
	}

}

// @Override
// public void beforeRun() {
// // has been inserted to fix a bug with joker tables
// // java -ea abscon.Resolution problems.real.tal.Tal ~/instances/tal/compiler2solver/fr.observed.tuples 9 27-35-38-22-15-13-26-28 -1
// // -s=all -t=120s -f=cop -ev -varh=DDegOnDom -rs
// // if (decremental)
// // Arrays.fill(lastSizesStack[0], -2);
// // else
// // Arrays.fill(lastSizes, -2);
// // lastDepth = 0;
// }
