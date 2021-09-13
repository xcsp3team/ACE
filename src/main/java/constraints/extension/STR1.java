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

import constraints.ConstraintExtension.ExtensionSpecific;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import problem.Problem;
import sets.SetDenseReversible;
import variables.Variable;

/**
 * This is STR (Simple Tabular Reduction), for filtering extension (table) constraints, as introduced by Julian Ullmann: "Partition search for non-binary
 * constraint satisfaction". Inf. Sci. 177(18): 3639-3678 (2007).
 * 
 * @author Christophe Lecoutre
 *
 */
public class STR1 extends ExtensionSpecific {

	/**********************************************************************************************
	 * Implementing Interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.tuples = ((Table) extStructure()).tuples;
		if (!(this instanceof CT)) { // because CT has very specific structures
			this.set = new SetDenseReversible(tuples.length, problem.variables.length + 1);
			this.ac = Variable.litterals(scp).booleanArray();
			this.cnts = new int[scp.length];
		}
		control(tuples.length > 0);
	}

	@Override
	public void restoreBefore(int depth) {
		if (set != null) // if not CT
			set.restoreLimitAtLevel(depth);
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
	public SetDenseReversible set;

	/**
	 * When used during filtering, ac[x][a] indicates if a support has been found for (x,a)
	 */
	protected boolean[][] ac;

	/**
	 * When used during filtering, cnts[x] is the number of values in the current domain of x with no found support (yet)
	 */
	protected int[] cnts;

	/**
	 * The total number of values over all variables in the scope of this constraint with no found support (yet)
	 */
	protected int cnt;

	/**********************************************************************************************
	 * Methods
	 *********************************************************************************************/

	/**
	 * Builds an extension constraint, with STR1 as specific filtering method
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public STR1(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length > 1, "Arity must be at least 2");
	}

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new Table(this);
	}

	/**
	 * Performs some initializations before starting the filtering process.
	 */
	protected void beforeFiltering() {
		cnt = 0;
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			cnt += (cnts[x] = doms[x].size());
			Arrays.fill(ac[x], false);
		}
	}

	/**
	 * Updates the domains of the variables in the scope of the constraint at the end of the filtering process
	 * 
	 * @return false if an inconsistency (empty domain) is detected
	 */
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
		int depth = problem.solver.depth();
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
