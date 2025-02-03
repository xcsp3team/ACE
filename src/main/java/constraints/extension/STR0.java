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

import static org.xcsp.common.Constants.STAR;
import static utility.Kit.control;

import java.util.Arrays;

import constraints.ConstraintExtension.ExtensionSpecific;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import problem.Problem;
import sets.SetDense;
import variables.Variable;

/**
 * This is a basic form of STR (Simple Tabular Reduction), for filtering extension (table) constraints. It can be used when the table is small (avoiding
 * consuming too much memory).
 * 
 * @author Christophe Lecoutre
 */
public class STR0 extends ExtensionSpecific {

	/**********************************************************************************************
	 * Implementing Interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction(int n) {
		super.afterProblemConstruction(n);
		this.tuples = ((Table) extStructure()).tuples;
		control(tuples.length > 0);
		this.set = new SetDense(tuples.length, true);
	}

	@Override
	public void restoreBefore(int depth) {
		set.fill();
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	/**
	 * The tuples of the table (redundant field)
	 */
	protected int[][] tuples;

	/**
	 * The reversible dense set storing the indexes (of tuples) of the current table
	 */
	public SetDense set;

	/**
	 * When used during filtering, ac[x][a] indicates if a support has been found for (x,a)
	 */
	protected boolean[][] ac;

	/**
	 * When used during filtering, cnts[x] is the number of values in the current domain of x with no found support (yet)
	 */
	protected int[] cnts;

	/**
	 * The number of variables for which support searching must be done (i.e., variables with some values that still must be checked to be AC)
	 */
	protected int sSupSize;

	/**
	 * The (dense) set of positions of variables for which support searching must be done. Relevant positions are at indexes from 0 to sSupSize (excluded).
	 */
	protected final int[] sSup;

	/**********************************************************************************************
	 * Methods
	 *********************************************************************************************/

	/**
	 * Builds an extension constraint, with STR0 as specific filtering method
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public STR0(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length > 1, "Arity must be at least 2");
		this.ac = Variable.litterals(scp).booleanArray();
		this.cnts = new int[scp.length];
		this.sSup = new int[scp.length];
	}

	@Override
	protected final ExtensionStructure buildExtensionStructure() {
		return new Table(this);
	}

	/**
	 * Performs some initializations before starting the filtering process.
	 */
	protected void beforeFiltering() {
		// int depth = problem.solver.depth();
		// for the moment, pb with /home/lecoutre/workspaceJv/ace/build/resources/main/csp/Dubois-10.xml.lzma
		// sValSize = 0;
		// for (int x = scp.length - 1; x >= 0; x--) {
		// int lr = scp[x].dom.lastRemovedLevel();
		// if (lr >= depth)
		// sVal[sValSize++] = x;
		// }
		sSupSize = 0;
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			cnts[x] = doms[x].size();
			sSup[sSupSize++] = x;
			Arrays.fill(ac[x], false);
		}
	}

	boolean universal;

	private boolean isValidTuple(int[] t) {
		// for (int i = sValSize - 1; i >= 0; i--) {
		// int x = sVal[i];
		// if (tuple[x] != STAR && !doms[x].contains(tuple[x]))
		// return false;
		// }
		universal = true;
		for (int x = t.length - 1; x >= 0; x--) {
			if (t[x] == STAR)
				continue;
			if (!doms[x].contains(t[x]))
				return false;
			if (doms[x].size() > 1)
				universal = false;
		}
		return true;
	}

	/**
	 * Updates the domains of the variables in the scope of the constraint at the end of the filtering process
	 * 
	 * @return false if an inconsistency (empty domain) is detected
	 */
	protected boolean updateDomains() {
		for (int i = sSupSize - 1; i >= 0; i--) {
			int x = sSup[i];
			int nRemovals = cnts[x];
			assert nRemovals > 0;
			if (doms[x].remove(ac[x], nRemovals) == false)
				return false;
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			if (isValidTuple(tuple)) {
				if (universal)
					return entail();
				for (int j = sSupSize - 1; j >= 0; j--) {
					int x = sSup[j];
					int a = tuple[x];
					if (a == STAR) {
						cnts[x] = 0;
						sSup[j] = sSup[--sSupSize];
					} else if (!ac[x][a]) {
						ac[x][a] = true;
						if (--cnts[x] == 0)
							sSup[j] = sSup[--sSupSize];
					}
				}
			} else
				set.removeAtPosition(i);
		}
		return updateDomains();
	}
}
