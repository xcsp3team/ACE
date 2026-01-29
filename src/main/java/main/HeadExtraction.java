/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package main;

import static utility.Kit.control;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.stream.IntStream;

import constraints.Constraint;
import dashboard.Input;
import learning.IpsReasoner.LearningIps;
import problem.Problem;
import problem.Problem.SymmetryBreaking;
import solver.Solver;
import solver.Solver.Stopping;
import utility.Kit;
import utility.Stopwatch;
import variables.Variable;

/**
 * This is the class of the main object (head) in charge of extracting an unsatisfiable core.
 * 
 * @author Christophe Lecoutre
 */
public final class HeadExtraction extends Head {

	/**
	 * Different ways of conducting extraction
	 */
	public enum Extraction {
		DEC_VAR, DEC_CON, VAR, CON, INC, INC_FIRST, MAX_CSP;
	}

	public static boolean[] and(boolean[] inOut, boolean[] in) {
		assert inOut.length == in.length;
		for (int i = 0; i < inOut.length; i++)
			inOut[i] = inOut[i] && in[i];
		return inOut;
	}

	public static boolean isSubsumed(boolean[] t1, boolean[] t2) {
		assert t1.length == t2.length;
		for (int i = 0; i < t1.length; i++)
			if (t1[i] && !t2[i])
				return false;
		return true;
	}

	public static final boolean isInducedBy(Variable x, boolean[] presentConstraints) {
		for (Constraint c : x.ctrs)
			if (presentConstraints[c.num])
				return true;
		return false;
	}

	/**
	 * The list of collected cores
	 */
	public List<List<Constraint>> cores = new ArrayList<>();

	/**
	 * Global array to denote the variables that are currently present. If presentVars[i] = false, then this variable
	 * has been removed (logically).
	 */
	private boolean[] presentVars;

	/**
	 * Global array to denote the constraints that are currently present. If presentCtrs[i] = false, then this
	 * constraint has been removed (logically).
	 */
	private boolean[] presentCtrs;

	/**
	 * Temporary Arrays used when looking for a transition variable and/or constraint.
	 */
	private boolean[] localVars, localCtrs;

	/**
	 * Temporary Array used when performing wcore
	 */
	private boolean[] activeCtrs;

	private boolean[] tmpVars, tmpCtrs;

	private VarComparator varComparator = new VarComparator();

	private CtrComparator ctrComparator = new CtrComparator();

	public int nRuns;

	private class VarComparator implements Comparator<Variable> {
		private List<Variable> core;

		private VarComparator core(List<Variable> core) {
			this.core = core;
			return this;
		}

		@Override
		public int compare(Variable x, Variable y) {
			boolean b1 = core.contains(x), b2 = core.contains(y);
			return b1 && !b2 ? -1 : !b1 && b2 ? 1 : Double.compare(y.wdegOnDom(), x.wdegOnDom());
		}
	}

	private class CtrComparator implements Comparator<Constraint> {
		private List<Constraint> core;

		private boolean wmode;

		private CtrComparator coreAndMode(List<Constraint> core, boolean wmode) {
			this.core = core;
			this.wmode = wmode;
			return this;
		}

		@Override
		public int compare(Constraint c1, Constraint c2) {
			boolean b1 = core.contains(c1), b2 = core.contains(c2);
			return b1 && !b2 ? -1
					: !b1 && b2 ? 1 : wmode ? Double.compare(c2.wdeg(), c1.wdeg()) : Integer.compare(c2.nEffectiveFilterings, c1.nEffectiveFilterings);
		}
	}

	private Variable[] arrayOfPossiblyPresentVars() {
		return IntStream.range(0, presentVars.length).filter(i -> presentVars[i]).mapToObj(i -> problem.variables[i]).toArray(Variable[]::new);
	}

	private Constraint[] arrayOfPossiblyPresentCtrs() {
		return IntStream.range(0, presentCtrs.length).filter(i -> presentCtrs[i]).mapToObj(i -> problem.constraints[i]).toArray(Constraint[]::new);
	}

	private boolean[] updatePresentVariablesFrom(boolean[] presentVars, boolean[] presentCtrs) {
		for (int i = 0; i < presentVars.length; i++)
			presentVars[i] = presentVars[i] && isInducedBy(problem.variables[i], presentCtrs);
		return presentVars;
	}

	private boolean[] updatePresentConstraintsFrom(boolean[] presentVars, boolean[] presentCtrs) {
		for (int i = 0; i < presentCtrs.length; i++)
			presentCtrs[i] = presentCtrs[i] && problem.constraints[i].isScopeCoveredBy(presentVars);
		return presentCtrs;
	}

	private void updatePossiblyArrays(Variable[] currVars, int min) {
		for (int i = min; i < currVars.length; i++)
			presentVars[currVars[i].num] = false;
		for (int i = 0; i < presentCtrs.length; i++)
			if (presentCtrs[i])
				presentCtrs[i] = problem.constraints[i].isScopeCoveredBy(presentVars);
	}

	private void updatePossiblyArrays(Constraint[] currCtrs, int min) {
		for (int i = min; i < currCtrs.length; i++)
			presentCtrs[currCtrs[i].num] = false;
		for (int i = 0; i < presentVars.length; i++)
			if (presentVars[i])
				presentVars[i] = isInducedBy(problem.variables[i], presentCtrs);
	}

	private boolean solveCurrentNetwork(boolean[] presentVars, boolean[] presentCtrs, boolean preserveWeightedDegrees) {
		nRuns++;
		problem.reduceTo(presentVars, presentCtrs);
		solver.reset();
		solver.solve();
		return solver.solutions.found > 0;
	}

	private boolean solveFor(boolean[] presentVars, Variable[] currVars, int min, int max, int center) {
		for (int i = min; i <= center; i++)
			presentVars[currVars[i].num] = true;
		for (int i = center + 1; i <= max; i++)
			presentVars[currVars[i].num] = false;
		return solveCurrentNetwork(presentVars, updatePresentConstraintsFrom(presentVars, tmpCtrs), true);
	}

	private boolean solveFor(boolean[] presentCtrs, Constraint[] currCtrs, int min, int max, int center) {
		for (int i = min; i <= center; i++)
			presentCtrs[currCtrs[i].num] = true;
		for (int i = center + 1; i <= max; i++)
			presentCtrs[currCtrs[i].num] = false;
		return solveCurrentNetwork(updatePresentVariablesFrom(tmpVars, presentCtrs), presentCtrs, true);
	}

	private List<Variable> minimalCoreOfVars() {
		Kit.log.info("Start Finding Minimal Core of variables ...");
		List<Variable> core = new ArrayList<>();
		for (boolean finished = false; !finished;) {
			Variable[] currVars = arrayOfPossiblyPresentVars();
			Arrays.sort(currVars, varComparator.core(core));
			Arrays.fill(localVars, false);
			int min = core.size(), max = currVars.length - 1;
			for (int i = 0; i < min; i++)
				localVars[currVars[i].num] = true;
			while (min != max) {
				int center = min + (max - min) / 2;
				if (!solveFor(localVars, currVars, min, max, center))
					max = center;
				else
					min = center + 1;
			}
			if (min == core.size())
				finished = true;
			// if finished, we check that the current core is not unsat by itself
			boolean transitionVariable = !finished || solveFor(localVars, currVars, min, currVars.length - 1, min - 1);
			if (transitionVariable) {
				core.add(currVars[min]);
				Kit.log.info("Last transition variable : " + currVars[min] + " coreSize=" + core.size());
			}
			updatePossiblyArrays(currVars, min + (transitionVariable ? 1 : 0));
		}
		assert !solveCurrentNetwork(presentVars, presentCtrs, true);
		Kit.log.info("End Finding Minimal Core of variables.");
		return core;
	}

	private List<Constraint> minimalCoreOfCtrs() {
		Kit.log.info("Start Finding Minimal Core of constraints (dichotomic) ...");
		List<Constraint> core = new ArrayList<>();
		for (boolean finished = false; !finished;) {
			Constraint[] currCtrs = arrayOfPossiblyPresentCtrs();
			Arrays.sort(currCtrs, ctrComparator.coreAndMode(core, solver.stopping != Stopping.FULL_EXPLORATION));
			Arrays.fill(localCtrs, false);
			int min = core.size(), max = currCtrs.length - 1;
			for (int i = 0; i < min; i++)
				localCtrs[currCtrs[i].num] = true;
			while (min != max) {
				int center = min + (max - min) / 2;
				if (!solveFor(localCtrs, currCtrs, min, max, center))
					max = center;
				else
					min = center + 1;
			}
			if (min == core.size())
				finished = true;
			// if finished, we check that the current core is not unsat by itself
			boolean transitionConstraint = !finished || solveFor(localCtrs, currCtrs, min, currCtrs.length - 1, min - 1);
			if (transitionConstraint) {
				core.add(currCtrs[min]);
				Kit.log.info("Last transition constraint : " + currCtrs[min] + " coreSize=" + core.size());
			}
			updatePossiblyArrays(currCtrs, min + (transitionConstraint ? 1 : 0));
		}
		assert !solveCurrentNetwork(presentVars, presentCtrs, true);
		Kit.log.info("End Finding Minimal Core of constraints.");
		return core;
	}

	private boolean wcore() {
		if (solveCurrentNetwork(presentVars, presentCtrs, true))
			return false;
		Kit.log.info("Start wcore ...");
		int nPreviousActiveConstraints = Integer.MAX_VALUE;
		while (true) {
			int nActiveConstraints = 0;
			Arrays.fill(activeCtrs, false);
			// for (Constraint ctr : problem.constraints) ctr.resetNbEffectiveFilterings();
			for (Constraint c : problem.constraints) {
				if (c.ignored)
					continue;
				if (c.nEffectiveFilterings > 0) {
					activeCtrs[c.num] = true;
					nActiveConstraints++;
				}
			}
			Kit.log.info("nEffectiveFilteringConstraints= " + nActiveConstraints + "\n");
			if (nActiveConstraints >= nPreviousActiveConstraints)
				break;
			nPreviousActiveConstraints = nActiveConstraints;
			control(isSubsumed(activeCtrs, presentCtrs));
			and(presentCtrs, activeCtrs);
			boolean sat = solveCurrentNetwork(updatePresentVariablesFrom(presentVars, presentCtrs), presentCtrs, true);
			control(!sat);
		}
		Kit.log.info("End wcore.");
		return true;
	}

	private void buildOrInitializeStructures(List<List<Constraint>> cores) {
		int n = problem.variables.length, e = problem.constraints.length;
		if (cores.size() == 0) {
			presentVars = new boolean[n];
			presentCtrs = new boolean[e];
			Arrays.fill(presentVars, true);
			Arrays.fill(presentCtrs, true);
			localVars = new boolean[n];
			localCtrs = new boolean[e];
			activeCtrs = new boolean[e];
			tmpVars = new boolean[n];
			tmpCtrs = new boolean[e];
		} else {
			Arrays.fill(presentVars, true);
			Arrays.fill(presentCtrs, true);
			cores.stream().forEach(core -> core.stream().forEach(c -> presentCtrs[c.num] = false));
			updatePresentVariablesFrom(presentVars, presentCtrs);
		}
	}

	@Override
	protected void solveInstance(int i) {
		problem = buildProblem(i);
		solver = buildSolver(problem);
		Stopwatch stopwatch = new Stopwatch();
		cores.clear();
		for (int cnt = 0; cnt < control.extraction.nCores; cnt++) {
			stopwatch.start();
			buildOrInitializeStructures(cores);
			if (!wcore()) {
				Kit.log.info("No more cores");
				break;
			}
			if (control.extraction.method == Extraction.VAR)
				minimalCoreOfVars();
			List<Constraint> core = minimalCoreOfCtrs();
			cores.add(core);
			Kit.log.config("\tNew core in wck = " + (stopwatch.wckTimeInSeconds()) + " and nRuns = " + nRuns);
		}
	}

	@Override
	public Problem buildProblem(int i) {
		if (problem == null)
			problem = super.buildProblem(i);
		else
			problem.reset();
		return problem;
	}

	public List<Constraint> lastCore() {
		return cores.size() == 0 ? null : cores.get(cores.size() - 1);
	}

	public HeadExtraction(String controlFileName) {
		super(controlFileName);
	}

	public HeadExtraction() {
		this(null);
	}

	/**
	 * Starts the main function of the constraint solver ACE (when extracting unsatisfiable cores of a CSP instance)
	 * 
	 * @param args
	 *            arguments specified by the user
	 */
	public static void main(String[] args) {
		Input.loadArguments(args);
		HeadExtraction extraction = new HeadExtraction();
		control(extraction.control.problem.symmetryBreaking == SymmetryBreaking.NO,
				() -> "Do not use symmetry breaking method when extracting unsatisfiable cores.");
		control(extraction.control.learning.ips == LearningIps.NO, () -> "Do not use partial state learning when extracting unsatisfiable cores.");
		// what about nogood recording from restarts?
		control(extraction.control.solving.clazz.equals(Solver.class.getSimpleName()), () -> extraction.control.solving.clazz);
		extraction.start();
	}

}
