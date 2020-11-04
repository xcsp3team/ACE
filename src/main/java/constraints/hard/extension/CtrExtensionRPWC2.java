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

import problem.Problem;
import utility.Kit;
import variables.Variable;

public final class CtrExtensionRPWC2 extends CtrExtensionRPWC {

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		if (!decremental) {
			this.lastSizes = Kit.repeat(-2, scp.length);
		} else {
			this.lastSizesStack = new int[pb.variables.length + 1][scp.length];
			Arrays.fill(lastSizesStack[0], -2);
		}
	}

	@Override
	public void restoreBefore(int depth) {
		super.restoreBefore(depth);
		if (!decremental)
			Arrays.fill(lastSizes, -2);
		else
			lastDepth = Math.max(0, Math.min(lastDepth, depth - 1));
		// if (entailedDepth >= depth) entailedDepth = -1;
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	private boolean decremental; // true if we exploit decrementality

	private int lastDepth;

	private int[] lastSizes; // 1D = variable position ; value = last domain sizes

	private int[][] lastSizesStack; // 1D = level ; 2D = variable position

	private int sValSize;
	private int[] sVal; // positions of the variables for which validity must be checked

	private int sSupSize;
	private int[] sSup; // positions of the variables for which GAC must be checked

	protected long nbAssignmentsAtLastCall = 0;

	public CtrExtensionRPWC2(Problem pb, Variable[] scp) {
		super(pb, scp);
		this.decremental = pb.rs.cp.settingExtension.decremental;
	}

	protected void manageLastPastVariable() {
		long nb = pb.solver.stats.nAssignments;
		if (nbAssignmentsAtLastCall != nb) {
			nbAssignmentsAtLastCall = nb;
			Variable lastPast = pb.solver.futVars.lastPast();
			int x = lastPast == null ? -1 : positionOf(lastPast);
			if (x != -1) {
				// scores[nbValVariables] = lastSizes[pos] / (double) domainElements[pos].getCurrentSize();
				sVal[sValSize++] = x;
			}
		}
	}

	@Override
	protected final void beforeFiltering() {
		if (decremental) {
			int depth = pb.solver.depth();
			assert depth >= lastDepth && lastDepth >= 0;
			for (int i = lastDepth + 1; i <= depth; i++)
				System.arraycopy(lastSizesStack[lastDepth], 0, lastSizesStack[i], 0, scp.length);
			lastSizes = lastSizesStack[depth];
			lastDepth = depth;
		}
		sValSize = sSupSize = 0;
		manageLastPastVariable();
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			int domSize = scp[x].dom.size();
			cnts[x] = domSize;
			if (lastSizes[x] != domSize) {
				sVal[sValSize++] = x;
				lastSizes[x] = domSize;
			}
			sSup[sSupSize++] = x;
			Arrays.fill(ac[x], false);
		}
	}

	@Override
	protected boolean updateDomains() {
		for (int i = 0; i < sSupSize; i++) {
			int x = sSup[i];
			int nRemovals = cnts[x];
			assert nRemovals > 0;
			if (!scp[x].dom.remove(ac[x], nRemovals))
				return false;
			lastSizes[x] = scp[x].dom.size();
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		pb.stuff.updateStatsForSTR(set);
		int depth = pb.solver.depth();
		// if (entailedDepth >= depth) return true;
		beforeFiltering();
		setIntersectionsToBeChecked();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			boolean valid = true;
			for (int j = sValSize - 1; j >= 0; j--) {
				int x = sVal[j];
				if (!doms[x].isPresent(tuple[x])) {
					valid = false;
					break;
				}
			}
			if (valid && checkStampsFor(tuple)) {
				for (int j = sSupSize - 1; j >= 0; j--) {
					int x = sSup[j];
					int a = tuple[x];
					if (!ac[x][a]) {
						if (--cnts[x] == 0)
							sSup[j] = sSup[--sSupSize];
						ac[x][a] = true;
					}
				}
			} else
				set.removeAtPosition(i, depth);
		}
		// if (Variable.computeNbValidTuplesFor(scope) == denseSetOfTuples.getSize()) { entailedDepth = depth; }
		updateLastTargetTimes();
		return updateDomains();
	}
}
