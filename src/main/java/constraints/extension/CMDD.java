/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension;

import static utility.Kit.control;

import java.util.Arrays;

import org.xcsp.common.Constants;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Transition;

import constraints.ConstraintExtension.ExtensionSpecific;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.MDD;
import constraints.extension.structures.MDD.Node;
import interfaces.Tags.TagPositive;
import interfaces.Tags.TagStarredCompatible;
import problem.Problem;
import sets.SetSparseReversible;
import variables.Domain;
import variables.Variable;

/**
 * This is the code for CMDD, as described in: "An MDD-based generalized arc consistency algorithm for positive and
 * negative table constraints and some global constraints", Constraints An Int. J. 15(2): 265-304 (2010) by K. Cheng and
 * R. Yap.
 * 
 * @author Christophe Lecoutre
 */
public abstract class CMDD extends ExtensionSpecific implements TagPositive {

	/**********************************************************************************************
	 * Implementing Interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction(int n) {
		super.afterProblemConstruction(n);
		this.mdd = (MDD) extStructure();
		this.trueNodes = new int[mdd.nNodes()];
		if (extOptions.decremental)
			this.set = new SetSparseReversible(mdd.nNodes(), n + 1, false);
		else
			this.falseNodes = new int[mdd.nNodes()];
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
	 * Class members
	 *********************************************************************************************/

	/**
	 * The MDD giving the semantics of the constraint
	 */
	protected MDD mdd;

	/**
	 * The reversible sparse set storing the indexes (of nodes) of the current MDD
	 */
	protected SetSparseReversible set;

	/**
	 * ac[x][a] indicates if a support has been found for (x,a); actually, x denotes the level where the variable is
	 * managed in the MDD
	 */
	protected boolean[][] ac;

	/**
	 * cnts[x] is the number of values in the current domain of x with no found support (yet); actually, x denotes the
	 * level where the variable is managed in the MDD
	 */
	protected int[] cnts;

	/**
	 * TheThe total number of values over all variables in the scope of this constraint with no found support (yet)
	 */
	protected int cnt;

	protected int falseTimestamp = 1, trueTimestamp = 1;

	/**
	 * Used to record, during filtering, the false nodes, i.e., the nodes that cannot lead to the terminal node
	 */
	protected int[] falseNodes;

	/**
	 * Used to record, during filtering, the true nodes, i.e., the nodes that can lead to the terminal node
	 */
	protected int[] trueNodes;

	protected int earlyCutoff;

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new MDD(this);
	}

	public CMDD(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length >= 1);
	}

	public CMDD(Problem pb, Variable[] scp, int[][] tuples) {
		this(pb, scp);
		storeTuples(tuples, true);
	}

	/**
	 * Performs some initializations before starting the filtering process.
	 */
	private void beforeFiltering() {
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

	/**
	 * Updates the domains of the variables in the scope of the constraint at the end of the filtering process
	 * 
	 * @return false if an inconsistency (empty domain) is detected
	 */
	private boolean updateDomains() {
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

	/**
	 * Method to be called when the terminal node has been shown to be reached from the specified level with the
	 * specified value index
	 * 
	 * @param level
	 *            a level in the MDD (corresponding to a variable)
	 * @param a
	 *            value index for the variable at the specified level
	 * @return true if the current exploration from the parent node can be terminated (due to early cutoff)
	 */
	protected boolean manageSuccessfulExploration(final int level, final int a) {
		int cutoffVariant = extOptions.variant;
		boolean future = !scp[level].assigned();
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

	protected abstract boolean recursiveExploration(Node node);

	/**
	 * Explores the MDD from the specified node so as to find supports
	 * 
	 * @param node
	 *            a node in the MDD
	 * @return true if the terminal (true) node can be reached (while following valid branches) from the specified node
	 */
	protected boolean explore(Node node) {
		if (node == Node.nodeT || trueNodes[node.num] == trueTimestamp)
			return true;
		if (node == Node.nodeF || (set != null && set.contains(node.num)) || (set == null && falseNodes[node.num] == falseTimestamp))
			return false;
		boolean supported = recursiveExploration(node);
		if (supported)
			trueNodes[node.num] = trueTimestamp;
		else if (set != null)
			set.add(node.num, problem.solver.depth());
		else
			falseNodes[node.num] = falseTimestamp;
		return supported;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		beforeFiltering();
		explore(mdd.root);
		return updateDomains();
	}

	/**********************************************************************************************
	 * CMDD
	 *********************************************************************************************/

	/**
	 * This is the code for CMDD, when dealing with ordinary tables
	 */
	public static final class CMDDO extends CMDD {

		public CMDDO(Problem pb, Variable[] scp) {
			super(pb, scp);
		}

		public CMDDO(Problem pb, Variable[] scp, int[][] tuples) {
			super(pb, scp, tuples);
		}

		public CMDDO(Problem pb, Variable[] scp, Node root) {
			this(pb, scp);
			this.extStructure = new MDD(this, root);
		}

		public CMDDO(Problem pb, Variable[] scp, Transition[] transitions) {
			this(pb, scp);
			String mddKey = signature() + " " + transitions;
			// TODO be careful, we assume above that the address of transitions can be used. Is that correct?
			this.extStructure = problem.head.structureSharing.mapForMDDs.computeIfAbsent(mddKey, r -> new MDD(this, transitions));
			// what about the key?
		}

		public CMDDO(Problem pb, Variable[] scp, Automaton automaton) {
			this(pb, scp);
			this.extStructure = new MDD(this, automaton);
		}

		public CMDDO(Problem pb, Variable[] scp, int[] coeffs, Object limits) {
			this(pb, scp);
			this.extStructure = new MDD(this, coeffs, limits);
		}

		@Override
		protected boolean recursiveExploration(Node node) {
			Domain dom = scp[node.level].dom;
			boolean supported = false, finished = false;
			if (dom.size() < node.nRelevantSons() || node.classes == null) {
				for (int a = dom.first(); a != -1 && !finished; a = dom.next(a)) {
					if (explore(node.sons[a])) {
						supported = true;
						finished = manageSuccessfulExploration(node.level, a);
					}
				}
			} else {
				search: for (int[] childsClass : node.classes) {
					for (int a : childsClass) {
						if (dom.contains(a) && explore(node.sons[a])) {
							supported = true;
							finished = manageSuccessfulExploration(node.level, a);
							if (finished)
								break search;
						}
					}
				}
			}
			return supported;
		}
	}

	/**********************************************************************************************
	 * CMDDShort
	 *********************************************************************************************/

	/**
	 * This is the code for CMDD, when dealing with starred tables
	 */
	public static final class CMDDS extends CMDD implements TagStarredCompatible {

		public CMDDS(Problem pb, Variable[] scp) {
			super(pb, scp);
		}

		public CMDDS(Problem pb, Variable[] scp, int[][] tuples) {
			super(pb, scp, tuples);
		}

		@Override
		protected boolean manageSuccessfulExploration(final int level, final int a) {
			if (a != Constants.STAR)
				return super.manageSuccessfulExploration(level, a);
			Domain dom = scp[level].dom;
			if (!scp[level].assigned()) {
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

		@Override
		protected boolean recursiveExploration(Node node) {
			Domain dom = scp[node.level].dom;
			boolean supported = false, finished = false;
			// if (dom.size() < node.nSonsDifferentFromNodeF()) {
			if (explore(node.sons[node.sons.length - 1])) {
				supported = true;
				manageSuccessfulExploration(node.level, Constants.STAR);
			}
			for (int a = dom.first(); a != -1 && !finished; a = dom.next(a)) {
				if (explore(node.sons[a])) {
					supported = true;
					finished = manageSuccessfulExploration(node.level, a);
				}
			}
			// } else {
			// search: for (int[] childsClass : node.sonsClasses) {
			// for (int a : childsClass) {
			// if (dom.isPresent(a) && exploreMDD(node.sons[a])) {
			// supported = true;
			// finished = manageSuccessfulExploration(node.level, a);
			// if (finished)
			// break search;
			// } } } }
			return supported;
		}
	}

}
