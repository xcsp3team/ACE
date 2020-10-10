/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search;

import static utility.Kit.log;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeFramework;
import org.xcsp.modeler.entities.VarEntities.VarAlone;
import org.xcsp.modeler.entities.VarEntities.VarArray;
import org.xcsp.modeler.entities.VarEntities.VarEntity;

import constraints.Constraint;
import constraints.CtrHard;
import problem.Problem;
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

	public String lastSolutionXml;

	/**
	 * Stores all solutions found by the solver. Only used (different from null) if the tag <code> recordSolutions </code> in the configuration file
	 * is set to <code> true </code>.
	 */
	public final List<int[]> allSolutions;

	private SolutionOptimizer solutionOptimizer;

	private AtomicBoolean competitionLock = new AtomicBoolean();

	public final String listVars, listVarsWithoutAuxiliary;

	private String vars_values(boolean considerVars, boolean discardAuxiliary) {
		StringBuilder sb = new StringBuilder();
		for (VarEntity va : solver.pb.varEntities.allEntities) {
			if (solver.pb.undisplay.contains(va.id) || (discardAuxiliary && va.id.startsWith(Problem.AUXILIARY_VARIABLE_PREFIX)))
				continue;
			if (considerVars)
				sb.append(" ").append(va.id).append(va instanceof VarArray ? ((VarArray) va).getEmptyStringSize() : "");
			else {
				if (va instanceof VarAlone)
					sb.append(" ").append(((Variable) ((VarAlone) va).var).lastSolutionPrettyAssignedValue); // .dom.prettyAssignedValue());
				else
					sb.append(" ").append(Variable.rawInstantiationOf(VarArray.class.cast(va).vars));
			}
		}
		return sb.append(" ").toString(); // one whitespace at both ends
	}

	public String lastSolutionInXmlFormat() { // auxiliary variables are not considered
		StringBuilder sb = new StringBuilder("<instantiation id='sol").append(nSolutionsFound).append("' type='solution'");
		sb.append(solver.pb.framework != TypeFramework.CSP ? " cost='" + bestBound + "'" : "").append(">");
		sb.append(" <list>").append(listVarsWithoutAuxiliary).append(" </list> <values>").append(vars_values(false, true));
		String s = sb.append("</values> </instantiation>").toString();
		if (lastSolutionXml != null)
			lastSolutionXml = s;
		return s;
	}

	public String lastSolutionInJsonFormat(boolean discardAuxiliary) {
		String PREFIX = "   ";
		StringBuilder sb = new StringBuilder(PREFIX).append("{\n");
		for (VarEntity va : solver.pb.varEntities.allEntities) {
			if (solver.pb.undisplay.contains(va.id) || (discardAuxiliary && va.id.startsWith(Problem.AUXILIARY_VARIABLE_PREFIX)))
				continue;
			sb.append(PREFIX).append(" ").append(va.id).append(": ");
			if (va instanceof VarAlone)
				sb.append(((Variable) ((VarAlone) va).var).lastSolutionPrettyAssignedValue); // dom.prettyAssignedValue());
			else
				sb.append(Variable.instantiationOf(VarArray.class.cast(va).vars, PREFIX));
			sb.append(",\n");
		}
		sb.delete(sb.length() - 2, sb.length());
		return sb.append("\n").append(PREFIX).append("}").toString();
	}

	public SolutionManager(Solver solver, long nSolutionsLimit) {
		this.solver = solver;
		this.nSolutionsLimit = nSolutionsLimit;
		this.bestBound = solver.rs.cp.settingOptimization.upperBound;
		this.allSolutions = solver.rs.cp.settingGeneral.recordSolutions ? new ArrayList<int[]>() : null;
		this.solutionOptimizer = new SolutionOptimizer(this);
		if (solver.rs.cp.settingXml.competitionMode)
			Runtime.getRuntime().addShutdownHook(new Thread(() -> displayFinalResults()));
		this.listVars = vars_values(true, false);
		this.listVarsWithoutAuxiliary = vars_values(true, true);
		// this.lastSolutionXml = ""; // security hard coding
	}

	public void displayFinalResults() {
		boolean fullExploration = solver.stoppingType == EStopping.FULL_EXPLORATION;
		synchronized (competitionLock) {
			if (!competitionLock.get()) {
				competitionLock.set(true);
				System.out.println();
				if (nSolutionsFound > 0)
					System.out.println("\nLast Solution in JSON format:\n" + lastSolutionInJsonFormat(true));
				if (fullExploration) {
					if (nSolutionsFound == 0)
						System.out.println("s UNSATISFIABLE");
					else
						System.out.println(solver.pb.framework == TypeFramework.COP ? "s OPTIMUM FOUND" : "s SATISFIABLE");
				} else {
					if (nSolutionsFound == 0)
						System.out.println("s UNKNOWN");
					else
						System.out.println(solver.pb.framework == TypeFramework.COP ? "s BOUND FOUND " + bestBound : "s SATISFIABLE");
				}
				if (nSolutionsFound > 0)
					System.out.println("v " + (lastSolutionXml != null ? lastSolutionXml : lastSolutionInXmlFormat()));

				System.out.println("\nd WRONG_DECISIONS " + solver.stats.nWrongDecisions);
				if (solver.solManager.nSolutionsFound > 1)
					System.out.println("d N_SOLUTIONS " + solver.solManager.nSolutionsFound);
				if (fullExploration)
					System.out.println("d COMPLETE");
				System.out.flush();
			}
		}
	}

	public void storeSolution(int[] t) {
		Variable[] variables = solver.pb.variables;
		assert t == null || t.length == variables.length;
		lastSolution = lastSolution == null ? new int[variables.length] : lastSolution;
		for (int i = 0; i < lastSolution.length; i++) {
			lastSolution[i] = t != null ? t[i] : variables[i].dom.unique();
			variables[i].lastSolutionPrettyAssignedValue = variables[i].dom.prettyAssignedValue();
		}
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
		// The following code must stay after storeSolution
		String s = lastSolutionInXmlFormat(); // keep the call separated in order to possibly secure its quick output (see code)
		if (!solver.rs.cp.settingXml.competitionMode)
			log.config(" " + s + "\n");
		if (solver.rs.cp.verbose > 1)
			log.config(lastSolutionInJsonFormat(false) + "\n");
		// solver.pb.api.prettyDisplay(vars_values(false, false).split("\\s+"));

		if (nSolutionsFound % 100000 == 0)
			log.fine("    " + nSolutionsFound + " solutions found " + " mem=" + Kit.getFormattedUsedMemorySize());

		if (solver.restarter instanceof RestarterLocalBranching)
			((RestarterLocalBranching) solver.restarter).enterLocalBranching();
	}

	public void handleNewSolutionAndPossiblyOptimizeIt() {
		handleNewSolution(true);
		solutionOptimizer.optimizeCurrentSolution();
	}

	// public void displayFinalResults() {
	// boolean fullExploration = solver.stoppingType == EStopping.FULL_EXPLORATION;
	// if (solver.rs.cp.settingXml.competitionMode) {
	// synchronized (solver.rs.competitionLock) {
	// if (!solver.rs.competitionLock.get()) {
	// solver.rs.competitionLock.set(true);
	// System.out.println();
	// if (lastSolutionX != null)
	// System.out.println("v " + lastSolutionX);
	// if (nSolutionsFound == 0)
	// System.out.println(fullExploration ? "s UNSATISFIABLE" : "s UNKNOWN");
	// else {
	// System.out.println(fullExploration && solver.pb.framework == TypeFramework.COP ? "s OPTIMUM FOUND" : "s SATISFIABLE");
	// }
	// System.out.println("\nd WRONG_DECISIONS " + solver.stats.nWrongDecisions);
	// if (solver.solManager.nSolutionsFound > 1)
	// System.out.println("d N_SOLUTIONS " + solver.solManager.nSolutionsFound);
	// System.out.flush();
	// }
	// }
	// } else {
	// Kit.log.config("\n<wrong> " + solver.stats.nWrongDecisions + " </wrong>");
	// if (nSolutionsFound == 0)
	// Kit.log.config(fullExploration ? "<unsatisfiable/>" : "<unknown/>");
	// else {
	// Kit.log.config((solver.pb.framework == TypeFramework.CSP ? "<satisfiable/>"
	// : fullExploration ? "<optimum> " + bestBound + " </optimum>" : "<bound> " + bestBound + " </bound>"));
	// if (solver.pb.framework == TypeFramework.CSP)
	// Kit.log.config("<nbSolutions> " + (fullExploration ? "" : "at least ") + nSolutionsFound + " </nbSolutions>");
	// }
	// System.out.flush();
	// }
	// }

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