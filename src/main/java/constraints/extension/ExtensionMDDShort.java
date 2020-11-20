/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension;

import static org.xcsp.modeler.definitions.IRootForCtrAndObj.map;

import java.util.Arrays;
import java.util.Map;

import org.xcsp.common.Constants;
import org.xcsp.modeler.definitions.DefXCSP;
import org.xcsp.modeler.definitions.ICtr.ICtrMdd;

import constraints.extension.Extension.ExtensionGlobal;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.MDDNodeShort;
import constraints.extension.structures.MDDShort;
import interfaces.TagPositive;
import interfaces.TagShort;
import problem.Problem;
import sets.SetSparseReversible;
import variables.Domain;
import variables.Variable;

public final class ExtensionMDDShort extends ExtensionGlobal implements TagPositive, TagShort, ICtrMdd {

	/**********************************************************************************************
	 * Interfaces
	 *********************************************************************************************/

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		int nNodes = ((MDDShort) extStructure).nNodes();
		this.trueNodes = new int[nNodes];
		if (pb.head.control.settingExtension.decremental)
			this.set = new SetSparseReversible(nNodes, false, pb.variables.length + 1);
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

	public ExtensionMDDShort(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length >= 1);
	}

	public ExtensionMDDShort(Problem pb, Variable[] scp, int[][] tuples) {
		this(pb, scp);
		key = signature() + " " + tuples + " " + true; // TDODO be careful, we assume that the address of tuples can be used
		storeTuples(tuples, true);
	}

	public ExtensionMDDShort(Problem pb, Variable[] scp, MDDNodeShort root) {
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

	private boolean manageSuccessfulExploration(int level, int a) {
		if (a == Constants.STAR) {
			Variable x = scp[level];
			if (x.isFuture()) {
				for (int b = x.dom.first(); b != -1; b = x.dom.next(b)) {
					if (!ac[level][b]) {
						cnt--;
						cnts[level]--;
						ac[level][b] = true;
					}
				}
			}
			return false;
		}

		int cutoffVariant = pb.head.control.settingExtension.variant;
		if (cutoffVariant == 2) {
			if (scp[level].isFuture()) {
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
			if (scp[level].isFuture()) {
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
		if (scp[level].isFuture()) {
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
		if (node == MDDNodeShort.nodeF || (set != null && set.isPresent(node.id)) || (set == null && falseNodes[node.id] == falseTimestamp))
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
			set.add(node.id, pb.solver.depth());
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

	@Override
	public Map<String, Object> mapXCSP() {
		return map(SCOPE, scp, LIST, compactOrdered(scp), TRANSITIONS, ((MDDShort) extStructure).root.getTransitions(Variable.buildDomainsArrayFor(scp)));
	}

	@Override
	public DefXCSP defXCSP() {
		return ICtrMdd.super.defXCSP();
	}
}
