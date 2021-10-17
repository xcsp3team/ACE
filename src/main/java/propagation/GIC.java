/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package propagation;

import static utility.Kit.control;

import java.util.stream.Stream;

import constraints.Constraint;
import constraints.extension.STR1;
import constraints.extension.STR3;
import heuristics.HeuristicVariables;
import heuristics.HeuristicVariablesDynamic.WdegOnDom;
import solver.Solver;
import solver.Solver.Stopping;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This is the class for Global Inverse Consistency (GIC). This kind of consistency is very strong as once enforced, it
 * guarantees that each literal (x,a) belongs to at least one solution. It can only be executes on some special
 * problems. For example, see "Computing and restoring global inverse consistency in interactive constraint
 * satisfaction", Artif. Intell. 241: 153-169 (2016) by C. Bessiere, H. Fargier, and C. Lecoutre.
 * 
 * @author Christophe Lecoutre
 */
public class GIC extends StrongConsistency { // GIC is GIC1

	/**
	 * The heuristic used to find solutions when enforcing this consistency
	 */
	protected HeuristicVariables heuristic;

	/**
	 * nInverseTest[x] is the number of times a value in the domain of x has been checked to be GIC
	 */
	public int[] nInverseTests;

	/**
	 * Indicates the total number of times a literal (i.e., a value for a variable) has been checked to be GIC
	 */
	public int nTotalInverseTests;

	private long limitBackup;

	/**
	 * Builds for the specified solver a propagation object that enforces GIC (Global Inverse Consistency).
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public GIC(Solver solver) {
		super(solver);
		this.heuristic = new WdegOnDom(solver, false);
		this.nInverseTests = new int[solver.problem.variables.length + 1];
		this.limitBackup = solver.solutions.limit;
		control(solver.head.control.restarts.cutoff == Long.MAX_VALUE, () -> "With GIC, there is currently no possibility of restarts.");
		control(Stream.of(solver.problem.constraints).allMatch(c -> !c.getClass().isAssignableFrom(STR3.class)),
				() -> "GIC currently not compatible with STR3");

	}

	/**
	 * Code to be executed when a new solution, involving the literal (x,a), has been found. For the base class, there
	 * is nothing to do.
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            a value index for x
	 */
	protected void handleNewSolution(Variable x, int a) {
	}

	/**
	 * Checks if the literal (x,a) is GIC; if it is not the case, deletes it.
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            a value index for x
	 * @return true if the literal (x,a) is GIC
	 */
	protected final boolean isInverse(Variable x, int a) {
		nInverseTests[solver.depth()]++;
		nTotalInverseTests++;
		solver.resetNoSolutions();
		solver.assign(x, a);
		HeuristicVariables heuristicBackup = solver.heuristic;
		solver.heuristic = heuristic;
		solver.solutions.limit = 1; // enough to check GIC
		boolean inverse = enforceACafterAssignment(x) && solver.doRun().stopping == Stopping.REACHED_GOAL;
		solver.solutions.limit = limitBackup; // we restore the initial limit
		solver.heuristic = heuristicBackup;
		if (inverse)
			handleNewSolution(x, a);
		else
			Kit.log.info(x + "=" + a + " is not inverse");
		solver.backtrack(x);
		return inverse;
	}

	protected final void updateSTRStructures() {
		for (Constraint c : solver.problem.constraints)
			if (c instanceof STR1) { // || constraint instanceof AllDifferent) {
				int bef = solver.problem.nValueRemovals;
				((STR1) c).runPropagator(null); // to update tables
				control(solver.problem.nValueRemovals == bef);
			}
	}

	protected void beforeFiltering() {
	}

	/**
	 * Enforces GIC by removing all values that are proved to be GIC-inconsistent
	 * 
	 * @return the number of deleted values
	 */
	protected int filtering() {
		int cnt = 0;
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			Domain dom = x.dom;
			for (int a = dom.first(); a != -1; a = dom.next(a))
				if (!isInverse(x, a)) {
					x.dom.removeElementary(a);
					cnt++;
				}
			control(dom.size() != 0, () -> "Not possible to reach inconsistency with GIC (or your instance is unsat)");
		}
		return cnt;
	}

	@Override
	public boolean enforceStrongConsistency() {
		performingProperSearch = true;
		beforeFiltering();
		long foundBackup = solver.solutions.found;
		int nValuesRemoved = filtering();
		if (verbose >= 1) // && nbValuesRemoved > 0)
			Kit.log.info("notGIC=" + nValuesRemoved + " at depth=" + solver.depth() + " for " + nInverseTests[solver.depth()] + " tests");
		solver.resetNoSolutions();
		solver.solutions.found = foundBackup;
		updateSTRStructures();
		performingProperSearch = false;
		return true;
	}

	/**********************************************************************************************
	 ***** Subclasses, including GIC2 and GIC3
	 *********************************************************************************************/

	public static abstract class GICAdvanced extends GIC {

		/**
		 * When used during filtering, cnts[x] is the number of values in the current domain of x that are not proved to
		 * be inverse (yet)
		 */
		protected int[] cnts;

		/**
		 * The number of variables for which GIC must still be checked (i.e., variables with some values that still must
		 * be checked to be GIC)
		 */
		protected int sSupSize;

		/**
		 * The (dense) set of variable numbers for which GIC must still be checked. Relevant positions are at indexes
		 * from 0 to sSupSize (excluded).
		 */
		protected int[] sSup;

		/**
		 * Global variable used by some methods during filtering
		 */
		protected int cursor;

		public GICAdvanced(Solver solver) {
			super(solver);
			this.cnts = new int[solver.problem.variables.length];
			this.sSup = new int[solver.problem.variables.length];
		}

		protected abstract boolean isInverseAdvanced(Variable x, int a);

		@Override
		protected int filtering() {
			int cnt = 0;
			for (cursor = sSupSize - 1; cursor >= 0; cursor--) {
				Variable x = solver.problem.variables[sSup[cursor]];
				if (cnts[x.num] == 0)
					continue;
				Domain dom = x.dom;
				for (int a = dom.first(); a != -1; a = dom.next(a))
					if (!isInverseAdvanced(x, a)) {
						x.dom.removeElementary(a);
						cnt++;
					}
				control(dom.size() != 0, () -> "Not possible to reach inconsistency with GIC (or your instance is unsat)");
			}
			return cnt;
		}

	}

	public static class GIC2 extends GICAdvanced {

		/**
		 * A global clock for GIC
		 */
		protected int timestamp;

		/**
		 * stamps[x][a] is the last time (x,a) has been checked to be GIC
		 */
		protected int[][] stamps;

		public GIC2(Solver solver) {
			super(solver);
			this.stamps = Variable.litterals(solver.problem.variables).intArray();
		}

		protected final void handleSolution(Variable x, int a, int[] solution) {
			for (int k = cursor - 1; k >= 0; k--) {
				int id = sSup[k];
				if (stamps[id][solution[id]] != timestamp) {
					stamps[id][solution[id]] = timestamp;
					cnts[id]--;
				}
			}
		}

		@Override
		protected void handleNewSolution(Variable x, int a) {
			handleSolution(x, a, solver.solutions.last);
		}

		@Override
		protected void beforeFiltering() {
			timestamp++;
			sSupSize = 0;
			for (Variable x : solver.futVars) {
				if (x.dom.size() > 1) {
					cnts[x.num] = x.dom.size();
					sSup[sSupSize++] = x.num;
				}
			}
		}

		@Override
		protected boolean isInverseAdvanced(Variable x, int a) {
			return stamps[x.num][a] == timestamp || isInverse(x, a);
		}
	}

	public static final class GIC3 extends GIC2 {

		/**
		 * residues[x][a] is the residual solution (i.e., last found solution) involving the literal (x,a)
		 */
		private int[][][] residues;

		public GIC3(Solver solver) {
			super(solver);
			this.residues = Stream.of(solver.problem.variables).map(x -> new int[x.dom.initSize()][]).toArray(int[][][]::new);
		}

		@Override
		protected void handleNewSolution(Variable x, int a) {
			int[] solution = solver.solutions.last;
			handleSolution(x, a, solution);
			if (residues[x.num][a] == null)
				residues[x.num][a] = new int[solver.problem.variables.length];
			Kit.copy(solution, residues[x.num][a]);
		}

		@Override
		protected boolean isInverseAdvanced(Variable x, int a) {
			if (stamps[x.num][a] == timestamp)
				return true;
			if (residues[x.num][a] != null && Variable.isValidTuple(solver.problem.variables, residues[x.num][a], true)) {
				handleSolution(x, a, residues[x.num][a]);
				return true;
			}
			return isInverse(x, a);
		}
	}

}
