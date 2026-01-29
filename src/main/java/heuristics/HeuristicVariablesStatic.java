/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package heuristics;

import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import interfaces.Observers.ObserverOnRuns;
import interfaces.Tags.TagMaximize;
import solver.Solver;
import utility.Kit;
import variables.Variable;

/**
 * This is the root class for building static variable ordering heuristics. It means that the order with which variables are assigned is computed at
 * initialization.
 * 
 * @author Christophe Lecoutre
 */
public abstract class HeuristicVariablesStatic extends HeuristicVariables implements ObserverOnRuns {

	@Override
	public final void beforeRun() {
		if (solver.restarter.numRun != 0 && solver.restarter.numRun % nbRunsBeforeReinitializing == 0)
			buildOrdering();
	}

	private int nbRunsBeforeReinitializing = Integer.MAX_VALUE; // hard coding

	/**
	 * The set of variables increasingly ordered by the static heuristic (the first one is the best one).
	 */
	private Variable[] ordering;

	private void buildOrdering() {
		// we build an ordered map with entries of the form (x, heuristic score of x multiplied by the optimization
		// coefficient) for every variable x
		Map<Variable, Double> map = Stream.of(solver.problem.variables).collect(Collectors.toMap(x -> x, x -> scoreOptimizedOf(x)));
		map = Kit.sort(map, (e1, e2) -> e1.getValue() < e2.getValue() ? -1 : e1.getValue() > e2.getValue() ? 1 : e1.getKey().num - e2.getKey().num);
		this.ordering = map.entrySet().stream().map(e -> e.getKey()).toArray(Variable[]::new);
		Kit.log.info("Static order of variables : " + Kit.join(ordering));
	}

	public HeuristicVariablesStatic(Solver solver, boolean anti) {
		super(solver, anti);
		buildOrdering();
	}

	@Override
	protected Variable bestUnpriorityVariable() {
		assert solver.problem.priorityVars.length == 0;
		for (int i = solver.propagation.performingProperSearch ? 0 : solver.futVars.nPast(); i < ordering.length; i++)
			if (!ordering[i].assigned()) // required in all cases? because possible proper search?
				return ordering[i];
		throw new AssertionError();
	}

	// ************************************************************************
	// ***** Subclasses
	// ************************************************************************

	/**
	 * This heuristic selects the next variable in the lexicographic order (using the number) of the variables.
	 */
	public static final class Lexico extends HeuristicVariablesStatic {

		public Lexico(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			return -x.num;
		}
	}

	public static final class Alternating extends HeuristicVariablesStatic {

		public Alternating(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			int n = solver.problem.variables.length;
			int score = x.num < n / 2 ? -2 * x.num : -2 * ((n - x.num) - 1) - 1;
			return -score;
		}
	}

	/**
	 * This heuristic selects the (first) variable with the highest degree
	 */
	public static final class Deg extends HeuristicVariablesStatic implements TagMaximize {

		public Deg(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.deg();
		}
	}

	/**
	 * This heuristic randomly selects a variable
	 */
	public static final class Srand extends HeuristicVariablesStatic {

		public Srand(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			return solver.head.random.nextDouble();
		}
	}

}