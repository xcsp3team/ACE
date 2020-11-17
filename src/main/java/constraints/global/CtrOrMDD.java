/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint.CtrGlobal;
import constraints.extension.structures.MDDCD;
import constraints.extension.structures.MDDNodeCD;
import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import problem.Problem;
import sets.SetDenseReversible;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class CtrOrMDD extends CtrGlobal implements TagGACGuaranteed, ObserverBacktrackingSystematic, TagFilteringCompleteAtEachCall {

	@Override
	public final boolean checkValues(int[] t) {
		for (MDDNodeCD root : roots) {
			MDDNodeCD node = root;
			for (int i = 0; !node.isLeaf(); i++)
				node = node.sons[t[i]];
			if (node == MDDNodeCD.nodeT)
				return true;
		}
		return false;
	}

	/**********************************************************************************************
	 * Implementing Interfaces
	 *********************************************************************************************/

	@Override
	public void restoreBefore(int depth) {
		validMdds.restoreLimitAtLevel(depth);
		for (SetSparseReversible set : sets)
			set.restoreLimitAtLevel(depth);

	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	MDDCD[] mdds;

	MDDNodeCD[] roots;

	SetDenseReversible validMdds;

	protected SetSparseReversible[] sets;

	protected boolean[][] ac; // ac[x][a] indicates if a support has been found for (x,a); actually, x denotes the level where the variable is managed
								// in the MDD

	protected int[] cnts; // cnts[x] is the number of values in the current domain of x with no found support (yet); actually, x denotes the level
							// where the variable is managed in the MDD

	protected int cnt; // The total number of values over all variables in the scope of this constraint with no found support (yet)

	protected int[][] trueNodes;

	protected int trueTimestamp = 1;

	protected int[] earlyCutoff;

	public CtrOrMDD(Problem pb, Variable[] scp, MDDCD[] mdds) {
		super(pb, scp);
		Kit.control(scp.length >= 1);
		this.mdds = mdds;
		this.roots = Stream.of(mdds).map(m -> m.root).toArray(MDDNodeCD[]::new);

		// for (MDDCD m : ms) {
		// System.out.println("GGG ");
		// m.root.display(0, new HashMap<>());
		// }
	}

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		// trueNodes = new HashSet<>();new int[nNodes];
		// if (pb.rs.cp.extension.decremental)
		trueNodes = IntStream.range(0, mdds.length).mapToObj(i -> new int[mdds[i].nNodes()]).toArray(int[][]::new);

		validMdds = new SetDenseReversible(mdds.length, pb.variables.length + 1); // new SetSparseReversible(mdds.length, true, pb.variables.length +
																					// 1);

		sets = IntStream.range(0, mdds.length).mapToObj(i -> new SetSparseReversible(mdds[i].nNodes(), false, pb.variables.length + 1))
				.toArray(SetSparseReversible[]::new);

		earlyCutoff = new int[mdds.length];

		ac = Variable.litterals(scp).booleanArray();
		cnts = new int[scp.length];

		for (MDDNodeCD root : roots)
			root.buildSonsClasses();

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
		// trueNodes.clear();
		Arrays.fill(earlyCutoff, scp.length);
	}

	private boolean manageSuccessfulExploration(int level, int a) { // , int i) {
		int cutoffVariant = pb.rs.cp.settingExtension.variant;
		// if (cutoffVariant == 2) {
		// if (scp[level].isFuture()) {
		// if (!ac[level][a]) {
		// cnt--;
		// cnts[level]--;
		// ac[level][a] = true;
		// if (cnts[level] == 0 && earlyCutoff[i] == level + 1)
		// earlyCutoff[i] = level;
		// }
		// } else if (earlyCutoff[i] == level + 1)
		// earlyCutoff[i] = level;
		// return level >= earlyCutoff[i];
		// }
		// if (cutoffVariant == 1) {
		// boolean b = false;
		// if (scp[level].isFuture()) {
		// if (!ac[level][a]) {
		// cnt--;
		// cnts[level]--;
		// ac[level][a] = true;
		// if (cnts[level] == 0 && earlyCutoff[i] == level + 1) {
		// earlyCutoff[i] = level;
		// b = true;
		// }
		// }
		// } else if (earlyCutoff[i] == level + 1) {
		// earlyCutoff[i] = level;
		// b = true;
		// }
		// return b;
		// }
		assert cutoffVariant == 0;
		if (scp[level].isFuture()) {
			if (!ac[level][a]) {
				// System.out.println(" foudn " + scp[level] + " " + a);
				cnt--;
				cnts[level]--;
				ac[level][a] = true;
			}
		}
		return false;
	}

	private boolean exploreMDD(int level, MDDNodeCD node, SetSparseReversible set, int[] trueNodes) { // , int i) {
		if (node == MDDNodeCD.nodeT || trueNodes[node.id] == trueTimestamp)
			return true;
		if (node == MDDNodeCD.nodeF || set.isPresent(node.id))
			return false;
		Domain dom = scp[level].dom;
		boolean supported = false, finished = false;

		if (dom.size() < node.nSonsDifferentFromNodeF()) {
			for (int a = dom.first(); a != -1 && !finished; a = dom.next(a)) {
				if (exploreMDD(level + 1, node.sons[a], set, trueNodes)) { // , i)) {
					supported = true;
					finished = manageSuccessfulExploration(level, a); // , i);
				}
			}
		} else {
			search: for (int[] childsClass : node.sonsClasses) {
				for (int a : childsClass) {
					if (dom.isPresent(a) && exploreMDD(level + 1, node.sons[a], set, trueNodes)) { // , i)) {
						supported = true;
						finished = manageSuccessfulExploration(level, a); // , i);
						if (finished)
							break search;
					}
				}
			}
		}

		// for (int a = dom.first(); a != -1 && !finished; a = dom.next(a)) {
		// if (exploreMDD(level + 1, node.sons[a], set, trueNodes, i)) {
		// supported = true;
		// finished = manageSuccessfulExploration(level, a, i);
		// }
		// }

		if (supported)
			trueNodes[node.id] = trueTimestamp;
		else
			set.add(node.id, pb.solver.depth());
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
		int depth = pb.solver.depth();

		for (int k = validMdds.limit; k >= 0; k--) {
			int i = validMdds.dense[k];
			// for (int i = 0; i < roots.length; i++)
			if (exploreMDD(0, roots[i], sets[i], trueNodes[i]) == false)
				validMdds.removeAtPosition(k, depth);
		}
		return updateDomains();
	}

}
