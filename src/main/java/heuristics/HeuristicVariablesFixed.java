/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics;

import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import interfaces.Observers.ObserverRuns;
import interfaces.Tags.TagMaximize;
import solver.Solver;
import utility.Kit;
import variables.Variable;

/**
 * This class gives the description of a static variable ordering heuristic. <br>
 * It means that the order of all variable assignments is computed at initialization (before each run).
 */
public abstract class HeuristicVariablesFixed extends HeuristicVariables implements ObserverRuns {

	private int nbRunsBeforeReinitializing = Integer.MAX_VALUE; // hard coding

	@Override
	public final void beforeRun() {
		if (solver.restarter.numRun != 0 && solver.restarter.numRun % nbRunsBeforeReinitializing == 0)
			buildOrdering();
	}

	@Override
	public final void afterRun() {
	}

	/** The set of variables increasingly ordered by the static heuristic (the first one is the best one). */
	private Variable[] ordering;

	private void buildOrdering() {
		// we build an ordered map with entries of the form (x, heuristic score of x multiplied by the optimization coefficient) for every variable x
		Map<Variable, Double> map = Stream.of(solver.problem.variables).collect(Collectors.toMap(x -> x, x -> scoreOptimizedOf(x)));
		map = Kit.sort(map, (e1, e2) -> e1.getValue() < e2.getValue() ? -1 : e1.getValue() > e2.getValue() ? 1 : e1.getKey().num - e2.getKey().num);
		ordering = map.entrySet().stream().map(e -> e.getKey()).toArray(Variable[]::new);
		Kit.log.info("Static order of variables : " + Kit.join(ordering));
	}

	public HeuristicVariablesFixed(Solver solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
		buildOrdering();
	}

	@Override
	protected Variable bestUnpriorityVar() {
		assert solver.problem.priorityVars.length == 0;
		for (int i = solver.propagation.performingProperSearch ? 0 : solver.futVars.nPast(); i < ordering.length; i++)
			if (ordering[i].isFuture()) // required in all cases because some variables may have been disconnected
				return ordering[i];
		throw new AssertionError();
	}

	// ************************************************************************
	// ***** Subclasses
	// ************************************************************************

	/**
	 * This heuristic, usually called <i>deg</i>, selects a (best evaluated) variable by considering an evaluation of the form deg(X) for any variable X.<br>
	 * Here, deg(X) denotes the (static) degree of the variable X.
	 */
	public static final class Deg extends HeuristicVariablesFixed implements TagMaximize {

		public Deg(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.deg();
		}
	}

	/**
	 * This heuristic, usually called <i>lexico</i>, selects the next variable in the lexicographic order (using the number) of the variables.
	 */
	public static final class Lexico extends HeuristicVariablesFixed {

		public Lexico(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			return -x.num;
		}
	}

	public static final class Srand extends HeuristicVariablesFixed {

		public Srand(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			return solver.head.random.nextDouble();
		}
	}

}