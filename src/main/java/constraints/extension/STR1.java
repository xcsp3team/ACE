/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension;

import static utility.Kit.control;

import java.util.Arrays;

import constraints.ConstraintExtension.ConstraintExtensionSpecific;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagNegative;
import problem.Problem;
import sets.SetDenseReversible;
import variables.Domain;
import variables.Variable;

/**
 * This is STR (Simple Tabular Reduction), for filtering extension (table) constraints, as introduced by Julian Ullmann: "Partition search for non-binary
 * constraint satisfaction". Inf. Sci. 177(18): 3639-3678 (2007).
 * 
 * @author Christophe Lecoutre
 */
public class STR1 extends ConstraintExtensionSpecific implements ObserverOnBacktracksSystematic {
	// TODO why not using a counter 'time' and replace boolean[][] ac by int[][] ac
	// we just do time++ instead of Arrays.fill(ac[x],false); the gain must be unnoticeable, right?

	/**********************************************************************************************
	 * Implementing Interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction(int n) {
		super.afterProblemConstruction(n);
		this.tuples = ((Table) extStructure()).tuples;
		control(this.tuples.length > 0);
		if (!(this instanceof CT)) // because CT (technically a subclass of STR1) has very specific structures
			this.set = new SetDenseReversible(tuples.length, n + 1);
	}

	@Override
	public void restoreBefore(int depth) {
		if (set != null) // i.e., if not CT
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
		boolean build = !(this instanceof CT || this instanceof STR2N);
		if (build) {
			this.ac = Variable.litterals(scp).booleanArray();
			this.cnts = new int[scp.length];
		}
	}

	@Override
	protected final ExtensionStructure buildExtensionStructure() {
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
			assert nRemovals < doms[x].size();
			doms[x].remove(ac[x], nRemovals); // no inconsistency possible
			// if (doms[x].remove(ac[x], nRemovals) == false)
			// return false;
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

		if (set.size() == 0)
			return dummy.dom.fail(); // inconsistency detected
		updateDomains();
		if (!extStructure.isStarred()) {
			int prod = 1;
			for (int i = futvars.limit; i >= 0; i--) {
				prod *= doms[futvars.dense[i]].size();
				if (prod > set.size())
					return true;
			}
			return prod == set.size() && entail();
		}
		return true;
		// return updateDomains();
	}

	/**********************************************************************************************
	 * STR1N
	 *********************************************************************************************/

	/**
	 * This is STR (Simple Tabular Reduction) for filtering negative extension (table) constraints.
	 * 
	 * @author Christophe Lecoutre
	 */
	public static final class STR1N extends STR1 implements TagNegative {

		/**
		 * nConflicts[x][a] indicates, during filtering, the number of valid conflicts encountered with (x,a)
		 */
		private final int[][] nConflicts;

		/**
		 * Builds an extension constraint, with STR1N as specific filtering method
		 * 
		 * @param pb
		 *            the problem to which the constraint is attached
		 * @param scp
		 *            the scope of the constraint
		 */
		public STR1N(Problem pb, Variable[] scp) {
			super(pb, scp);
			this.nConflicts = Variable.litterals(scp).intArray();
		}

		@Override
		protected void beforeFiltering() {
			super.beforeFiltering();
			for (int i = futvars.limit; i >= 0; i--)
				Arrays.fill(nConflicts[futvars.dense[i]], 0);
		}

		@Override
		public boolean runPropagator(Variable evt) {
			int depth = problem.solver.depth();
			beforeFiltering();
			for (int i = set.limit; i >= 0; i--) {
				int[] tuple = tuples[set.dense[i]];
				if (isValid(tuple)) {
					for (int j = futvars.limit; j >= 0; j--) {
						int x = futvars.dense[j];
						int a = tuple[x];
						nConflicts[x][a]++;
					}
				} else
					set.removeAtPosition(i, depth);
			}
			long nValidTuples = Domain.nValidTuplesBounded(doms);
			for (int i = futvars.limit; i >= 0; i--) {
				int x = futvars.dense[i];
				Domain dom = scp[x].dom;
				long limit = nValidTuples / dom.size();
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					if (nConflicts[x][a] != limit) {
						cnt--;
						cnts[x]--;
						ac[x][a] = true;
					}
				}
			}
			return updateDomains();
		}
	}
}
