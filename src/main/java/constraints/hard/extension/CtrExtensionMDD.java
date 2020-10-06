/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension;

import static org.xcsp.modeler.definitions.IRootForCtrAndObj.map;

import java.util.Arrays;
import java.util.Map;
import java.util.stream.Stream;

import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Transition;
import org.xcsp.modeler.definitions.DefXCSP;
import org.xcsp.modeler.definitions.ICtr.ICtrMdd;

import constraints.hard.CtrExtension;
import constraints.hard.extension.structures.ExtensionStructureHard;
import constraints.hard.extension.structures.MDD;
import constraints.hard.extension.structures.MDDNode;
import interfaces.FilteringGlobal;
import interfaces.TagGACGuaranteed;
import interfaces.TagPositive;
import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import problem.Problem;
import utility.Kit;
import utility.sets.SetSparseReversible;
import variables.Variable;
import variables.domains.Domain;

public final class CtrExtensionMDD extends CtrExtension implements FilteringGlobal, TagPositive, TagGACGuaranteed, ObserverBacktrackingSystematic, ICtrMdd {

	/**********************************************************************************************
	 * Implementing Interfaces
	 *********************************************************************************************/

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

	public CtrExtensionMDD(Problem pb, Variable[] scp) {
		super(pb, scp);
		Kit.control(scp.length >= 1);
	}

	public CtrExtensionMDD(Problem pb, Variable[] scp, int[][] tuples) {
		this(pb, scp);
		key = signature() + " " + tuples + " " + true; // TDODO be careful, we assume that the address of tuples can be used
		storeTuples(tuples, true);
	}

	public CtrExtensionMDD(Problem pb, Variable[] scp, MDDNode root) {
		this(pb, scp);
		extStructure = new MDD(this, root);
		initSpecificStructures();
	}

	public CtrExtensionMDD(Problem pb, Variable[] scp, Transition[] transitions) {
		this(pb, scp);
		// key = signature() + " " + transitions; // TDODO be careful, we assume that the address of tuples can be used
		extStructure = new MDD(this, Stream.of(transitions).map(t -> new Object[] { t.firstState, t.symbol, t.secondState }).toArray(Object[][]::new));
		initSpecificStructures();
	}

	public CtrExtensionMDD(Problem problem, Variable[] scope, Automaton automata) {
		this(problem, scope);
		extStructure = new MDD(this, automata);
		initSpecificStructures();
	}

	public CtrExtensionMDD(Problem problem, Variable[] scope, int[] coeffs, Object limits) {
		this(problem, scope);
		System.out.println("before mdd");
		extStructure = new MDD(this, coeffs, limits);
		System.out.println("after mdd");
		initSpecificStructures();
	}

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		int nNodes = ((MDD) extStructure).nNodes();
		trueNodes = new int[nNodes];
		if (pb.rs.cp.settingExtension.decremental)
			set = new SetSparseReversible(nNodes, false, pb.variables.length + 1);
		else
			falseNodes = new int[nNodes];
	}

	@Override
	protected ExtensionStructureHard buildExtensionStructure() {
		return new MDD(this);
	}

	@Override
	protected void initSpecificStructures() {
		ac = Variable.litterals(scp).booleanArray();
		cnts = new int[scp.length];
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
		int cutoffVariant = pb.rs.cp.settingExtension.variant;
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

	private boolean exploreMDD(MDDNode node) {
		if (node == MDDNode.nodeT || trueNodes[node.id] == trueTimestamp)
			return true;
		if (node == MDDNode.nodeF || (set != null && set.isPresent(node.id)) || (set == null && falseNodes[node.id] == falseTimestamp))
			return false;
		Domain dom = scp[node.level].dom;
		boolean supported = false, finished = false;
		if (dom.size() < node.nSonsDifferentFromNodeF()) {
			for (int a = dom.first(); a != -1 && !finished; a = dom.next(a)) {
				if (exploreMDD(node.sons[a])) {
					supported = true;
					finished = manageSuccessfulExploration(node.level, a);
				}
			}
		} else {
			search: for (int[] childsClass : node.sonsClasses) {
				for (int a : childsClass) {
					if (dom.isPresent(a) && exploreMDD(node.sons[a])) {
						supported = true;
						finished = manageSuccessfulExploration(node.level, a);
						if (finished)
							break search;
					}
				}
			}
		}
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
		exploreMDD(((MDD) extStructure).root);
		return updateDomains();
	}

	@Override
	public Map<String, Object> mapXCSP() {
		return map(SCOPE, scp, LIST, compactOrdered(scp), TRANSITIONS, ((MDD) extStructure).root.getTransitions(Variable.buildDomainsArrayFor(scp)));
	}

	@Override
	public DefXCSP defXCSP() {
		return ICtrMdd.super.defXCSP();
	}
}
