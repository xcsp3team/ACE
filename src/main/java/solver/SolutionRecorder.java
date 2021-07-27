/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package solver;

import static org.xcsp.common.Types.TypeFramework.COP;
import static org.xcsp.common.Types.TypeFramework.CSP;
import static org.xcsp.common.Types.TypeFramework.MAXCSP;
import static utility.Kit.GREEN;
import static utility.Kit.RED;
import static utility.Kit.log;
import static utility.Kit.preprint;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.modeler.entities.VarEntities.VarAlone;
import org.xcsp.modeler.entities.VarEntities.VarArray;
import org.xcsp.modeler.entities.VarEntities.VarEntity;

import constraints.Constraint;
import constraints.global.Sum;
import problem.Problem;
import utility.Enums.EStopping;
import utility.Kit;
import variables.Variable;

public final class SolutionRecorder {

	public final Solver solver;

	/**
	 * Number of solutions to be found, before stopping. When equal to PLUS_INFINITY, all solutions are searched for (no limit is fixed).
	 */
	public long limit;

	/**
	 * Number of solutions found by the solver so far. Initially, 0.
	 */
	public long found;

	/**
	 * For optimization problems, the best bound found by the solver if found > 0, the specified upper bound initially given otherwise
	 */
	public long bestBound;

	/**
	 * Array containing the last found solution (indexes of values, and not values), or null.
	 */
	public int[] lastSolution;

	public int lastSolutionRun = -1; // number of the run where the last solution has been found

	public String lastSolutionXml;

	/**
	 * Stores all solutions found by the solver. Only used (different from null) if the tag <code> recordSolutions </code> in the configuration file is set to
	 * <code> true </code>.
	 */
	public final List<int[]> allSolutions;

	// private SolutionOptimizer solutionOptimizer;

	private AtomicBoolean lock = new AtomicBoolean(); // important for competition

	public final String listVars, listVarsWithoutAuxiliary;

	private void update(Object object, List<Integer> list) {
		if (object == null)
			list.add(Constants.STAR);
		else if (object instanceof Variable)
			list.add(((Variable) object).dom.toVal(((Variable) object).valueIndexInLastSolution));
		else // recursive call
			Stream.of((Object[]) object).forEach(o -> update(o, list));
	}

	private void addls(int value, int cnt, List<String> ls) {
		String v = value == Constants.STAR ? Constants.STAR_SYMBOL : value + "";
		if (cnt > 1) // hard coding
			ls.add(v + Constants.TIMES + cnt);
		else
			for (int k = 0; k < cnt; k++)
				ls.add(v);
	}

	private String compactValues(boolean discardAuxiliary) {
		Kit.control(solver.problem.features.nSymbolicVars == 0);
		List<String> ls = new ArrayList<>();
		List<Integer> list = new ArrayList<>();
		for (VarEntity va : solver.problem.varEntities.allEntities) {
			if (solver.problem.undisplay.contains(va.id) || (discardAuxiliary && va.id.startsWith(Problem.AUXILIARY_VARIABLE_PREFIX)))
				continue;
			update(va instanceof VarAlone ? ((VarAlone) va).var : VarArray.class.cast(va).vars, list);
			int last = list.get(list.size() - 1);
			for (int i = list.size() - 2; i >= 0; i--)
				if (list.get(i) != last) {
					int prev = list.get(0);
					int cnt = 1;
					for (int j = 1; j <= i; j++) {
						if (list.get(j) == prev)
							cnt++;
						else {
							addls(prev, cnt, ls);
							prev = list.get(j);
							cnt = 1;
						}
					}
					addls(prev, cnt, ls);
					for (int j = 0; j <= i; j++)
						list.remove(0);
					break;
				}
		}
		addls(list.get(0), list.size(), ls);
		return ls.stream().collect(Collectors.joining(" "));
	}

	private String valsForXml(boolean compact, boolean discardAuxiliary) {
		if (compact && solver.problem.features.nSymbolicVars == 0)
			return compactValues(discardAuxiliary);
		StringBuilder sb = new StringBuilder();
		for (VarEntity va : solver.problem.varEntities.allEntities) {
			if (solver.problem.undisplay.contains(va.id) || (discardAuxiliary && va.id.startsWith(Problem.AUXILIARY_VARIABLE_PREFIX)))
				continue;
			if (sb.length() > 0)
				sb.append(" ");
			if (va instanceof VarAlone) {
				Variable x = (Variable) ((VarAlone) va).var;
				sb.append(x.dom.prettyValueOf(x.valueIndexInLastSolution));
			} else
				sb.append(Variable.rawInstantiationOf(VarArray.class.cast(va).vars));
		}
		return sb.toString();
	}

	private String varsForXml(boolean discardAuxiliary) {
		StringBuilder sb = new StringBuilder();
		for (VarEntity va : solver.problem.varEntities.allEntities) {
			if (solver.problem.undisplay.contains(va.id) || (discardAuxiliary && va.id.startsWith(Problem.AUXILIARY_VARIABLE_PREFIX)))
				continue;
			sb.append(sb.length() > 0 ? " " : "").append(va.id).append(va instanceof VarArray ? ((VarArray) va).getEmptyStringSize() : "");
		}
		return sb.toString();
	}

	public String lastSolutionInXmlFormat() { // auxiliary variables are not considered
		assert found > 0;
		StringBuilder sb = new StringBuilder("<instantiation id='sol").append(found).append("' type='solution'");
		sb.append(solver.problem.settings.framework != CSP ? " cost='" + bestBound + "'" : "").append(">");
		sb.append(" <list> ").append(listVarsWithoutAuxiliary).append(" </list> <values> ").append(valsForXml(solver.problem.settings.xmlCompact, true));
		String s = sb.append(" </values> </instantiation>").toString();
		if (lastSolutionXml != null)
			lastSolutionXml = s;
		return s;
	}

	public String lastSolutionInJsonFormat() {
		assert found > 0;
		boolean discardAuxiliary = !solver.head.control.general.jsonAux;
		String PREFIX = "   ";
		StringBuilder sb = new StringBuilder(PREFIX).append("{\n");
		for (VarEntity va : solver.problem.varEntities.allEntities) {
			if (solver.problem.undisplay.contains(va.id) || (discardAuxiliary && va.id.startsWith(Problem.AUXILIARY_VARIABLE_PREFIX)))
				continue;
			sb.append(PREFIX).append(" ").append(va.id).append(": ");
			if (va instanceof VarAlone) {
				Variable x = (Variable) ((VarAlone) va).var;
				sb.append(x.dom.prettyValueOf(x.valueIndexInLastSolution));
			} else
				sb.append(Variable.instantiationOf(VarArray.class.cast(va).vars, PREFIX));
			sb.append(",\n");
		}
		sb.delete(sb.length() - 2, sb.length());
		return sb.append("\n").append(PREFIX).append("}").toString();
	}

	public SolutionRecorder(Solver solver, long nSolutionsLimit) {
		this.solver = solver;
		this.limit = nSolutionsLimit;
		this.bestBound = solver.head.control.optimization.ub;
		this.allSolutions = solver.head.control.general.recordSolutions ? new ArrayList<int[]>() : null;
		// this.solutionOptimizer = new SolutionOptimizer(this);
		// if (solver.head.control.xml.competitionMode)
		Runtime.getRuntime().addShutdownHook(new Thread(() -> displayFinalResults()));
		this.listVars = varsForXml(false);
		this.listVarsWithoutAuxiliary = varsForXml(true);
		// this.lastSolutionXml = ""; // uncomment for security when really running a competition (hard coding)
	}

	public void displayFinalResults() {
		TypeFramework framework = solver.problem.settings.framework;
		boolean fullExploration = solver.stopping == EStopping.FULL_EXPLORATION;
		synchronized (lock) {
			if (!lock.get()) {
				lock.set(true);
				System.out.println();
				if (found > 0 && solver.problem.variables.length <= solver.head.control.general.jsonLimit)
					System.out.println("\n  Solution " + found + " in JSON format:\n" + lastSolutionInJsonFormat() + "\n");
				if (fullExploration) {
					if (found == 0)
						System.out.println(preprint("s UNSATISFIABLE", GREEN));
					else
						System.out.println(framework == COP ? preprint("s OPTIMUM FOUND", GREEN) : preprint("s SATISFIABLE", GREEN));
				} else {
					if (found == 0)
						System.out.println(preprint("s UNKNOWN", RED));
					else
						System.out.println(framework == COP ? preprint("s SATISFIABLE", GREEN) : preprint("s SATISFIABLE", GREEN));
				}
				if (found > 0)
					System.out.println("\n" + preprint("v", GREEN) + " " + (lastSolutionXml != null ? lastSolutionXml : lastSolutionInXmlFormat()));
				System.out.println("\n" + preprint("d WRONG DECISIONS", GREEN) + " " + solver.stats.nWrongDecisions);
				// if (framework == CSP)
				System.out.println(preprint("d NUMBER OF" + (fullExploration ? "" : " FOUND") + " SOLUTIONS", GREEN) + " " + found);
				if (framework == COP && found > 0)
					System.out.println(preprint("d BOUND " + bestBound, GREEN));
				System.out.println(fullExploration ? preprint("d COMPLETE EXPLORATION", GREEN) : preprint("d INCOMPLETE EXPLORATION", RED));
				System.out.println("\nc real time : " + solver.head.stopwatch.cpuTimeInSeconds());
				System.out.flush();
			}
		}
	}

	public void storeSolution(int[] t) {
		Variable[] variables = solver.problem.variables;
		assert t == null || t.length == variables.length;
		lastSolution = lastSolution == null ? new int[variables.length] : lastSolution;
		for (int i = 0; i < lastSolution.length; i++) {
			lastSolution[i] = t != null ? t[i] : variables[i].dom.single();
			variables[i].valueIndexInLastSolution = lastSolution[i]; // lastSolution[i]lastSolutionPrettyAssignedValue = variables[i].dom.prettyAssignedValue();
		}

		// SumSimpleLE c = (SumSimpleLE) solver.pb.optimizer.ctr;
		// Variable x = c.mostImpacting();
		// System.out.println("ccccc most " + x + " " + x.dom.toVal(lastSolution[x.num]));
	}

	private int h1 = -1, h2 = -1;

	private void solutionHamming() {
		if (found <= 1)
			return;
		h1 = (int) IntStream.range(0, lastSolution.length).filter(i -> lastSolution[i] != solver.problem.variables[i].dom.single()).count();
		if (solver.problem.optimizer != null) {
			Constraint c = (Constraint) solver.problem.optimizer.ctr;
			h2 = (int) IntStream.range(0, lastSolution.length)
					.filter(i -> lastSolution[i] != solver.problem.variables[i].dom.single() && c.involves(solver.problem.variables[i])).count();
		}
	}

	private Variable selectMostImpactingVariable() {
		Kit.control(solver.problem.optimizer != null && solver.problem.optimizer.ctr instanceof Sum);
		Constraint c = (Constraint) solver.problem.optimizer.ctr;

		return null;

	}

	/**
	 * This method is called when a new solution has been found by the solver.
	 */
	public void handleNewSolution(boolean controlSolution) {
		Kit.control(!controlSolution || controlFoundSolution());
		found++;
		lastSolutionRun = solver.restarter.numRun;
		solutionHamming();
		if (found >= limit)
			solver.stopping = EStopping.REACHED_GOAL;
		storeSolution(null);
		if (allSolutions != null)
			allSolutions.add(lastSolution.clone());
		solver.stats.manageSolution();

		if (solver.propagation.performingProperSearch)
			return;
		if (solver.problem.settings.framework == MAXCSP) {
			int z = (int) Stream.of(solver.problem.constraints).filter(c -> !c.checkCurrentInstantiation()).count();
			Kit.control(z < bestBound, () -> "z=" + z + " bb=" + bestBound);
			bestBound = z;
		} else if (solver.problem.optimizer != null) { // COP
			bestBound = solver.problem.optimizer.value();
			System.out.println(preprint("o " + bestBound, GREEN) + "  " + (solver.head.instanceStopwatch.wckTimeInSeconds()));
			// solver.restarter.currCutoff += 20;
			// + " \t#" + found); // + "); (hamming: " + h1 + ", in_objective: " + h2 + ")");
		}
		// The following code must stay after storeSolution
		if (solver.head.control.general.verbose > 1)
			log.config(lastSolutionInJsonFormat() + "\n");
		String s = lastSolutionInXmlFormat(); // keep the call separated in order to possibly secure its quick output (see code)
		if (solver.head.control.general.verbose > 2 || solver.head.control.general.xmlAllSolutions)
			log.config("     " + s);
		// solver.problem.api.prettyDisplay(vars_values(false, false).split("\\s+"));
	}

	public void handleNewSolution() {
		handleNewSolution(true);
		// solutionOptimizer.optimizeCurrentSolution();
	}

	private boolean controlFoundSolution() {
		if (solver instanceof Solver) {
			Variable x = Variable.firstNonSingletonVariableIn(solver.problem.variables);
			Kit.control(x == null, () -> "Problem with last solution: variable " + x + " has not a unique value");
			if (solver.problem.settings.framework == MAXCSP)
				return true;
		}
		Constraint c = Constraint.firstUnsatisfiedHardConstraint(solver.problem.constraints);
		Kit.control(c == null, () -> "Problem with last solution: constraint " + c + " " + c.getClass().getName() + " not satisfied : ");
		return true;
	}
}