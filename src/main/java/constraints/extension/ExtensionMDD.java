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
import java.util.stream.Stream;

import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Transition;
import org.xcsp.modeler.definitions.ICtr.ICtrMdd;

import constraints.extension.Extension.ExtensionGlobal;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.MDD;
import constraints.extension.structures.MDD.MDDNode;
import interfaces.Tags.TagPositive;
import problem.Problem;
import sets.SetSparseReversible;
import variables.Domain;
import variables.Variable;

public final class ExtensionMDD extends ExtensionGlobal implements TagPositive, ICtrMdd {

	/**********************************************************************************************
	 * Implementing Interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		int nNodes = ((MDD) extStructure).nNodes();
		this.trueNodes = new int[nNodes];
		if (problem.head.control.extension.decremental)
			this.set = new SetSparseReversible(nNodes, false, problem.variables.length + 1);
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

	public ExtensionMDD(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length >= 1);
	}

	public ExtensionMDD(Problem pb, Variable[] scp, int[][] tuples) {
		this(pb, scp);
		storeTuples(tuples, true);
	}

	public ExtensionMDD(Problem pb, Variable[] scp, MDDNode root) {
		this(pb, scp);
		extStructure = new MDD(this, root);
	}

	public ExtensionMDD(Problem pb, Variable[] scp, Transition[] transitions) {
		this(pb, scp);
		// key = signature() + " " + transitions; // TDODO be careful, we assume that the address of tuples can be used
		extStructure = new MDD(this, Stream.of(transitions).map(t -> new Object[] { t.firstState, t.symbol, t.secondState }).toArray(Object[][]::new));
	}

	public ExtensionMDD(Problem problem, Variable[] scope, Automaton automaton) {
		this(problem, scope);
		extStructure = new MDD(this, automaton);
	}

	public ExtensionMDD(Problem problem, Variable[] scope, int[] coeffs, Object limits) {
		this(problem, scope);
		extStructure = new MDD(this, coeffs, limits);
	}

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new MDD(this);
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
		int cutoffVariant = problem.head.control.extension.variant;
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
					if (dom.present(a) && exploreMDD(node.sons[a])) {
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
		exploreMDD(((MDD) extStructure).root);
		return updateDomains();
	}

}
