/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeFramework;

import constraints.Constraint;
import constraints.CtrHard;
import search.backtrack.RestarterLocalBranching;
import search.backtrack.SolverBacktrack;
import search.local.SolutionOptimizer;
import search.local.SolverLocal;
import utility.Enums.EStopping;
import utility.Kit;
import variables.Variable;

public final class SolutionManager {

	public final Solver solver;

	/**
	 * Number of solutions to be found, before stopping. When equal to PLUS_INFINITY, all solutions are searched for (no limit is fixed).
	 */
	public long nSolutionsLimit;

	/**
	 * Number of solutions found by the solver so far. Initially, 0.
	 */
	public long nSolutionsFound;

	/**
	 * For optimization problems, the best bound found by the solver if nbSolutionsFound > 0, the specified upper bound initially given otherwise
	 */
	public long bestBound;

	/**
	 * Array containing the last found solution (indexes of values, and not values), or null.
	 */
	public int[] lastSolution;

	public int lastSolutionRun = -1; // number of the run where the last solution has been found

	public String lastSolutionX;

	/**
	 * Stores all solutions found by the solver. Only used (different from null) if the tag <code> recordSolutions </code> in the configuration file
	 * is set to <code> true </code>.
	 */
	public final List<int[]> allSolutions;

	private SolutionOptimizer solutionOptimizer;

	public SolutionManager(Solver solver, long nSolutionsLimit) {
		this.solver = solver;
		this.nSolutionsLimit = nSolutionsLimit;
		this.bestBound = solver.rs.cp.settingOptimization.upperBound;
		this.allSolutions = solver.rs.cp.settingGeneral.recordSolutions ? new ArrayList<int[]>() : null;
		this.solutionOptimizer = new SolutionOptimizer(this);
	}

	public void storeSolution(int[] t) {
		assert t == null || t.length == solver.pb.variables.length;
		lastSolution = lastSolution == null ? new int[solver.pb.variables.length] : lastSolution;
		for (int i = 0; i < lastSolution.length; i++)
			lastSolution[i] = t != null ? t[i] : solver.pb.variables[i].dom.unique();
	}

	private int h1 = -1, h2 = -1;

	private void solutionHamming() {
		if (nSolutionsFound <= 1)
			return;
		h1 = (int) IntStream.range(0, lastSolution.length).filter(i -> lastSolution[i] != solver.pb.variables[i].dom.unique()).count();
		if (solver.pb.optimizationPilot != null) {
			Constraint c = (Constraint) solver.pb.optimizationPilot.ctr;
			h2 = (int) IntStream.range(0, lastSolution.length)
					.filter(i -> lastSolution[i] != solver.pb.variables[i].dom.unique() && c.involves(solver.pb.variables[i])).count();
		}
	}

	/**
	 * This method is called when a new solution has been found by the solver.
	 */
	public void handleNewSolution(boolean controlSolution) {
		Kit.control(!controlSolution || controlFoundSolution());
		nSolutionsFound++;
		lastSolutionRun = solver.restarter.numRun;
		solutionHamming();
		if (nSolutionsFound >= nSolutionsLimit)
			solver.stoppingType = EStopping.REACHED_GOAL;
		storeSolution(null);
		if (allSolutions != null)
			allSolutions.add(lastSolution.clone());
		solver.stats.manageSolution();

		if (solver.propagation.performingProperSearch)
			return;
		if (solver.pb.framework == TypeFramework.MAXCSP) {
			int z = (int) Stream.of(solver.pb.constraints).filter(c -> !((CtrHard) c).checkCurrentInstantiation()).count();
			Kit.control(z < bestBound, () -> "z=" + z + " bb=" + bestBound);
			bestBound = z;
			// solver.restarter.forceRootPropagation = true; // a garder ?

		} else if (solver.pb.optimizationPilot != null) {
			bestBound = solver.pb.optimizationPilot.value();
			Kit.control(solver.pb.optimizationPilot.isBetterBound(bestBound));
			// solver.restarter.forceRootPropagation = true;
			if (solver.rs.cp.settingXml.competitionMode)
				System.out.println("o " + bestBound + "  (hamming: " + h1 + ", in_objective: " + h2 + ")");
		}
		solver.pb.prettyDisplay();
		if (nSolutionsFound % 100000 == 0)
			Kit.log.fine("    " + nSolutionsFound + " solutions found " + " mem=" + Kit.getFormattedUsedMemorySize());

		if (solver.restarter instanceof RestarterLocalBranching)
			((RestarterLocalBranching) solver.restarter).enterLocalBranching();
	}

	public void handleNewSolutionAndPossiblyOptimizeIt() {
		handleNewSolution(true);
		solutionOptimizer.optimizeCurrentSolution();
	}

	public void displayFinalResults() {
		boolean fullExploration = solver.stoppingType == EStopping.FULL_EXPLORATION;
		if (solver.rs.cp.settingXml.competitionMode) {
			synchronized (solver.rs.competitionLock) {
				if (!solver.rs.competitionLock.get()) {
					solver.rs.competitionLock.set(true);
					System.out.println();
					if (lastSolutionX != null)
						System.out.println("v " + lastSolutionX);
					if (nSolutionsFound == 0)
						System.out.println(fullExploration ? "s UNSATISFIABLE" : "s UNKNOWN");
					else {
						System.out.println(fullExploration && solver.pb.framework == TypeFramework.COP ? "s OPTIMUM FOUND" : "s SATISFIABLE");
					}
					System.out.println("\nd WRONG_DECISIONS " + solver.stats.nWrongDecisions);
					if (solver.solManager.nSolutionsFound > 1)
						System.out.println("d N_SOLUTIONS " + solver.solManager.nSolutionsFound);
					System.out.flush();
				}
			}
		} else {
			Kit.log.config("\n<wrong> " + solver.stats.nWrongDecisions + " </wrong>");
			if (nSolutionsFound == 0)
				Kit.log.config(fullExploration ? "<unsatisfiable/>" : "<unknown/>");
			else {
				Kit.log.config((solver.pb.framework == TypeFramework.CSP ? "<satisfiable/>"
						: fullExploration ? "<optimum> " + bestBound + " </optimum>" : "<bound> " + bestBound + " </bound>"));
				if (solver.pb.framework == TypeFramework.CSP)
					Kit.log.config("<nbSolutions> " + (fullExploration ? "" : "at least ") + nSolutionsFound + " </nbSolutions>");
			}
			System.out.flush();
		}
	}

	public Constraint firstUnsatisfiedConstraint(int[] solution) {
		for (Constraint c : solver.pb.constraints) {
			if (c.ignored || !(c instanceof CtrHard))
				continue;
			int[] tmp = c.tupleManager.localTuple;
			for (int i = 0; i < tmp.length; i++)
				tmp[i] = solution != null ? solution[c.scp[i].num] : c.scp[i].dom.unique();
			if (((CtrHard) c).checkIndexes(tmp) == false)
				return c;
		}
		return null;
	}

	private boolean controlFoundSolution() {
		if (!(solver instanceof SolverLocal)) {
			Variable x = Variable.firstNonSingletonVariableIn(solver.pb.variables);
			Kit.control(x == null, () -> "Problem with last solution: variable " + x + " has not a unique value");
		}
		if (solver instanceof SolverBacktrack && solver.pb.framework == TypeFramework.MAXCSP)
			return true;
		Constraint c = firstUnsatisfiedConstraint(null);
		Kit.control(c == null, () -> "Problem with last solution: constraint " + c + " not satisfied : ");
		return true;
	}
}