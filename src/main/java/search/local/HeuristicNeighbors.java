/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package search.local;

import java.util.Random;

import org.xcsp.common.Types.TypeFramework;

import utility.Reflector;
import variables.Variable;
import variables.domains.Domain;

public abstract class HeuristicNeighbors {

	protected final SolverLocal solver;

	protected final TabuManager tabuManager;

	protected final int[] counters;

	protected final Random random;

	protected Variable bestVariable;

	protected int bestIndex;

	protected int bestEvolution;

	protected int localBestEvolution;

	protected Long currentCost = new Long(0);

	protected long bestCost;

	protected Variable lastAssignedVariable;

	protected int bestEvaluationEverSeen = Integer.MAX_VALUE;

	protected double bestCostEverSeen = Double.MAX_VALUE;

	public HeuristicNeighbors(SolverLocal solver) {
		this.solver = solver;
		this.tabuManager = Reflector.buildObject(solver.rs.cp.settingLocalSearch.classForTabu, TabuManager.class, solver, solver.rs.cp.settingLocalSearch.tabuListSize);
		this.counters = new int[solver.pb.variables.length];
		this.random = solver.rs.random;
	}

	protected int selectIndexWithLowestEvolution(Variable x, int evolutionLimit) {
		int tieSize = 0;
		int bestIndex = -1;
		localBestEvolution = evolutionLimit;
		bestCost = Long.MAX_VALUE;

		Domain dom = x.dom;
		for (int a = dom.first(); a != -1; a = dom.next(a)) {
			int evolution = solver.conflictManager.computeEvolutionFor(x, a, localBestEvolution, currentCost);
			if (evolution > localBestEvolution)
				continue;
			if (solver.conflictManager.currEvaluation() + evolution < bestEvaluationEverSeen)
				bestEvaluationEverSeen = solver.conflictManager.currEvaluation() + evolution;
			else if (tabuManager.isTabu(x, a))
				continue;
			if (evolution < localBestEvolution) {
				tieSize = 1;
				bestIndex = a;
				localBestEvolution = evolution;
				if (solver.pb.framework == TypeFramework.COP)
					bestCost = currentCost.longValue();
			} else {
				assert evolution == localBestEvolution;
				if (solver.pb.framework == TypeFramework.COP) {
					if (currentCost > bestCost)
						continue;
					if (currentCost < bestCost) {
						bestCost = currentCost;
						tieSize = 1;
						bestIndex = a;
						localBestEvolution = evolution;
					} else {
						tieSize++;
						if (random.nextDouble() < 1.0 / tieSize)
							bestIndex = a;
					}
				} else {
					tieSize++;
					if (random.nextDouble() < 1.0 / tieSize)
						bestIndex = a;
				}
			}
		}
		currentCost = bestCost;
		return bestIndex;
	}

	public abstract void selectNeighbor();

	public void setBestNeighbor() {
		selectNeighbor();
		solver.propagateDependentVariables();
		tabuManager.push(bestVariable, bestIndex);
		lastAssignedVariable = bestVariable;
		counters[bestVariable.num]++;
		solver.conflictManager.recomputeEvaluations();
		assert (solver.conflictManager.checkConflictingConstraints());
	}

	public static class BestGlobal extends HeuristicNeighbors {

		private int evaluationLimit = 0; // hard coding; put a value >= 0

		public BestGlobal(SolverLocal solver) {
			super(solver);
		}

		private void assess(Variable x, boolean b) {
			if (x == lastAssignedVariable || x.dom.size() == 1)
				return;
			int variableEvaluation = solver.conflictManager.currEvaluationOf(x);
			// a value >= 0, so -variableEvaluation is the best possible evolution
			if (bestEvolution < -variableEvaluation || (variableEvaluation < evaluationLimit) == b)
				return;
			int idx = selectIndexWithLowestEvolution(x, bestEvolution);
			if (idx == -1)
				return;

			assert localBestEvolution <= bestEvolution;
			if (localBestEvolution < bestEvolution) {
				bestVariable = x;
				bestIndex = idx;
				bestEvolution = localBestEvolution;
			} else {
				assert localBestEvolution == bestEvolution;
				if (counters[x.num] < counters[bestVariable.num]) {
					bestVariable = x;
					bestIndex = idx;
				}
			}
		}

		@Override
		public void selectNeighbor() {
			bestVariable = null;
			bestIndex = -1;
			bestEvolution = Integer.MAX_VALUE;

			Variable[] variables = solver.decisionVars;
			// Variable worstVariable = solver.getConflictManager().getWorstVariable();
			// int position = worstVariable.id;
			int position = random.nextInt(variables.length);
			for (int i = position; i < variables.length; i++)
				assess(variables[i], true);
			for (int i = 0; i < position; i++)
				assess(variables[i], true);
			if (evaluationLimit != 0 && bestEvolution > -evaluationLimit) {
				for (int i = position; i < variables.length; i++)
					assess(variables[i], false);
				for (int i = 0; i < position; i++)
					assess(variables[i], false);
			}
			// assert !tabuManager.isTabu(bestVariable, bestIndex) ||
			// localSearchSolver.getConflictManager.getCurrentEvaluation() + bestEvolution == bestEvaluationEverSeen;
		}
	}

	public static class BestLocal extends HeuristicNeighbors {

		public BestLocal(SolverLocal solver) {
			super(solver);
		}

		private Variable selectVariableWithLowestEvaluation() {
			int tieSize = 0;
			Variable bestVariable = null;
			int bestEvaluation = Integer.MAX_VALUE;

			for (Variable x : solver.pb.variables) {
				if (x == lastAssignedVariable)
					continue;
				int evaluation = solver.conflictManager.currEvaluationOf(x);
				if (evaluation < bestEvaluation) {
					tieSize = 1;
					bestVariable = x;
					bestEvaluation = evaluation;
				} else if (evaluation == bestEvaluation) {
					tieSize++;
					if (random.nextDouble() < 1.0 / tieSize)
						bestVariable = x;
				}
			}
			return bestVariable;
		}

		private boolean randomlySelectNeighbor() {
			if (random.nextFloat() < solver.rs.cp.settingLocalSearch.thresholdForRandomVariableSelection) {
				Variable[] variables = solver.pb.variables;
				bestVariable = variables[random.nextInt(variables.length)];
				// variable in conflict instead ??
				if (random.nextFloat() < solver.rs.cp.settingLocalSearch.thresholdForRandomValueSelection) {
					bestIndex = bestVariable.dom.random();
					int evaluation = solver.conflictManager.currEvaluation() + solver.conflictManager.computeEvolutionFor(bestVariable, bestIndex);
					if (evaluation < bestEvaluationEverSeen)
						bestEvaluationEverSeen = evaluation;
					return !tabuManager.isTabu(bestVariable, bestIndex);
				}
				bestIndex = selectIndexWithLowestEvolution(bestVariable, Integer.MAX_VALUE);
				return true;
			}
			return false;
		}

		@Override
		public void selectNeighbor() {
			if (!randomlySelectNeighbor()) {
				bestVariable = selectVariableWithLowestEvaluation();
				bestIndex = selectIndexWithLowestEvolution(bestVariable, Integer.MAX_VALUE);
			}
		}
	}

}
