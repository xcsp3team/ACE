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

import org.xcsp.common.Constants;

import constraints.ConstraintExtension.ExtensionSpecific;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.MDDShort;
import constraints.extension.structures.MDDShort.MDDNodeShort;
import interfaces.Tags.TagPositive;
import interfaces.Tags.TagStarredCompatible;
import problem.Problem;
import sets.SetSparseReversible;
import variables.Domain;
import variables.Variable;

public final class CMDDShort extends ExtensionSpecific implements TagPositive, TagStarredCompatible {

	/**********************************************************************************************
	 * Interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		int nNodes = ((MDDShort) extStructure()).nNodes();
		this.trueNodes = new int[nNodes];
		if (esettings.decremental)
			this.set = new SetSparseReversible(nNodes, problem.variables.length + 1, false);
		else
			this.falseNodes = new int[nNodes];
		this.ac = Variable.litterals(scp).booleanArray();
		this.cnts = new int[scp.length];
	}

	@Override
	public void restoreBefore(int depth) {
		if (set != null)
			set.restoreLimitAtLevel(depth);
		else
			falseTimestamp++;
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	protected SetSparseReversible set;

	protected boolean[][] ac; // ac[x][a] indicates if a support has been found for (x,a); actually, x denotes the level where the variable is managed
								// in the MDD

	protected int[] cnts; // cnts[x] is the number of values in the current domain of x with no found support (yet); actually, x denotes the level
							// where the variable is managed in the MDD

	protected int cnt; // The total number of values over all variables in the scope of this constraint with no found support (yet)

	protected int falseTimestamp = 1, trueTimestamp = 1;

	protected int[] falseNodes, trueNodes;

	protected int earlyCutoff;

	/**********************************************************************************************
	 * Methods
	 *********************************************************************************************/

	public CMDDShort(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length >= 1);
	}

	public CMDDShort(Problem pb, Variable[] scp, int[][] tuples) {
		this(pb, scp);
		storeTuples(tuples, true);
	}

	public CMDDShort(Problem pb, Variable[] scp, MDDNodeShort root) {
		this(pb, scp);
		extStructure = new MDDShort(this, root);
	}

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new MDDShort(this);
	}

	protected void beforeFiltering() {
		cnt = 0;
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			int domSize = scp[x].dom.size();
			cnt += domSize;
			cnts[x] = domSize;
			Arrays.fill(ac[x], false);
		}
		trueTimestamp++;
		earlyCutoff = scp.length;
	}

	private boolean manageSuccessfulExploration(final int level, final int a) {
		boolean future = !scp[level].assigned();
		if (a == Constants.STAR) {
			Domain dom = scp[level].dom;
			if (future) {
				for (int b = dom.first(); b != -1; b = dom.next(b)) {
					if (!ac[level][b]) {
						cnt--;
						cnts[level]--;
						ac[level][b] = true;
					}
				}
			}
			return false;
		}

		int cutoffVariant = esettings.variant;
		if (cutoffVariant == 2) {
			if (future) {
				if (!ac[level][a]) {
					cnt--;
					cnts[level]--;
					ac[level][a] = true;
					if (cnts[level] == 0 && earlyCutoff == level + 1)
						earlyCutoff = level;
				}
			} else if (earlyCutoff == level + 1)
				earlyCutoff = level;
			return level >= earlyCutoff;
		}
		if (cutoffVariant == 1) {
			boolean b = false;
			if (future) {
				if (!ac[level][a]) {
					cnt--;
					cnts[level]--;
					ac[level][a] = true;
					if (cnts[level] == 0 && earlyCutoff == level + 1) {
						earlyCutoff = level;
						b = true;
					}
				}
			} else if (earlyCutoff == level + 1) {
				earlyCutoff = level;
				b = true;
			}
			return b;
		}
		assert cutoffVariant == 0;
		if (future) {
			if (!ac[level][a]) {
				cnt--;
				cnts[level]--;
				ac[level][a] = true;
			}
		}
		return false;
	}

	private boolean exploreMDD(MDDNodeShort node) {
		if (node == MDDNodeShort.nodeT || trueNodes[node.id] == trueTimestamp)
			return true;
		if (node == MDDNodeShort.nodeF || (set != null && set.contains(node.id)) || (set == null && falseNodes[node.id] == falseTimestamp))
			return false;
		Domain dom = scp[node.level].dom;
		boolean supported = false, finished = false;
		// if (dom.size() < node.nSonsDifferentFromNodeF()) {
		if (exploreMDD(node.sons[node.sons.length - 1])) {
			supported = true;
			manageSuccessfulExploration(node.level, Constants.STAR);
		}
		for (int a = dom.first(); a != -1 && !finished; a = dom.next(a)) {
			if (exploreMDD(node.sons[a])) {
				supported = true;
				finished = manageSuccessfulExploration(node.level, a);
			}
		}
		// }
		// else {
		// search: for (int[] childsClass : node.sonsClasses) {
		// for (int a : childsClass) {
		// if (dom.isPresent(a) && exploreMDD(node.sons[a])) {
		// supported = true;
		// finished = manageSuccessfulExploration(node.level, a);
		// if (finished)
		// break search;
		// }
		// }
		// }
		// }
		if (supported)
			trueNodes[node.id] = trueTimestamp;
		else if (set != null)
			set.add(node.id, problem.solver.depth());
		else
			falseNodes[node.id] = falseTimestamp;
		return supported;

	}

	protected boolean updateDomains() {
		for (int i = futvars.limit; i >= 0 && cnt > 0; i--) {
			int x = futvars.dense[i];
			int nRemovals = cnts[x];
			if (nRemovals == 0)
				continue;
			if (scp[x].dom.remove(ac[x], nRemovals) == false)
				return false;
			cnt -= nRemovals;
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		beforeFiltering();
		exploreMDD(((MDDShort) extStructure).root);
		return updateDomains();
	}

}
