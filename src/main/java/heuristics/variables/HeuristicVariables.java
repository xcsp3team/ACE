/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics.variables;

import java.util.stream.Stream;

import dashboard.ControlPanel.SettingVarh;
import dashboard.ControlPanel.SettingVars;
import heuristics.Heuristic;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import variables.Variable;
import variables.domains.DomainHuge;

/**
 * This class gives the description of a variable ordering heuristic. <br>
 * A variable ordering heuristic is used by a backtrack search solver to select a variable (to be assigned) at each step of search. <br>
 * NB : do not modify the name of this class as it is used by reflection.
 */
public abstract class HeuristicVariables extends Heuristic {

	public static class BestScoredVariable {
		public Variable variable;
		public double score;

		private boolean minimization;

		public BestScoredVariable reset(boolean minimization) {
			variable = null;
			score = minimization ? Double.MAX_VALUE : Double.NEGATIVE_INFINITY;
			this.minimization = minimization;
			return this;
		}

		public boolean update(Variable x, double s) {
			if (minimization) {
				if (s < score) {
					variable = x;
					score = s;
					return true;
				}
			} else if (s > score) {
				variable = x;
				score = s;
				return true;
			}
			return false; // not updated
		}
	}

	protected BestScoredVariable bestScoredVariable = new BestScoredVariable();

	/** The backtrack search solver that uses this variable ordering heuristic. */
	protected final SolverBacktrack solver;

	/** The variables that must be assigned in priority. */
	protected Variable[] priorityVars;

	/**
	 * Relevant only if priorityVariables is not an array of size 0. Variables must be assigned in the order strictly given by priorityVariables from
	 * 0 to nbStrictPriorityVariables-1. Variables in priorityVariables recorded between nbStrictPriorityVariables and priorityVariables.length-1 must
	 * then be assigned in priority but in any order given by the heuristic. Beyond priorityVariables.length-1, the heuristic can select any future
	 * variable.
	 */
	private int nStrictlyPriorityVars;

	protected SettingVarh settings;

	public final void setPriorityVars(Variable[] priorityVars, int nbStrictPriorityVars) {
		this.priorityVars = priorityVars;
		this.nStrictlyPriorityVars = nbStrictPriorityVars;
	}

	public final void resetPriorityVars() {
		this.priorityVars = new Variable[0];
		this.nStrictlyPriorityVars = 0;
	}

	public HeuristicVariables(SolverBacktrack solver, boolean antiHeuristic) {
		super(antiHeuristic); // anti ? (this instanceof TagMinimize ? TypeOptimization.MAX : TypeOptimization.MIN ) : (this instanceof TagMinimize ?
								// TypeOptimization.MAX : TypeOptimization.MIN );
		this.solver = solver;
		SettingVars settingVars = solver.rs.cp.settingVars;
		if (settingVars.priorityVars.length > 0) {
			this.priorityVars = Stream.of(settingVars.priorityVars).map(o -> solver.pb.findVarWithNumOrId(o)).toArray(Variable[]::new);
			this.nStrictlyPriorityVars = settingVars.nStrictPriorityVars;
		} else {
			this.priorityVars = solver.pb.priorityVars;
			this.nStrictlyPriorityVars = solver.pb.nStrictPriorityVars;
		}
		this.settings = solver.rs.cp.varh;
	}

	/** Returns the score of the specified variable. This is the method to override when defining a new heuristic. */
	public abstract double scoreOf(Variable x);

	/** Returns the score of the specified variable, while considering the optimization coeff (i.e., minimization or maximization). */
	public final double scoreOptimizedOf(Variable x) {
		if (x.dom instanceof DomainHuge)
			return scoreCoeff == -1 ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY; // because such variables must be computed (and not
																							// assigned)
		return scoreOf(x) * scoreCoeff;
	}

	/** Returns the preferred variable among those that are priority. */
	private Variable bestPriorityVar() {
		int nPast = solver.futVars.nDiscarded();
		if (nPast < priorityVars.length) {
			if (nPast < nStrictlyPriorityVars)
				return priorityVars[nPast];
			if (settings.lastConflictSize > 0) {
				Variable x = solver.lcReasoner.lastConflictPriorityVar();
				if (x != null && Kit.isPresent(x, priorityVars))
					return x;
			}
			Variable bestVar = null;
			double bestScore = Double.NEGATIVE_INFINITY;
			for (int i = nStrictlyPriorityVars; i < priorityVars.length; i++) {
				if (priorityVars[i].isAssigned())
					continue;
				double score = scoreOptimizedOf(priorityVars[i]);
				if (score > bestScore) {
					bestVar = priorityVars[i];
					bestScore = score;
				}
			}
			return bestVar;
		}
		return null;
	}

	/** Returns the preferred variable among those that are not priority. Called only if no variable has been selected in priority. */
	protected abstract Variable bestUnpriorityVar();

	/** Returns the preferred variable (next variable to be assigned) of the problem. */
	public final Variable bestVar() {
		Variable x = bestPriorityVar();
		return x != null ? x : bestUnpriorityVar();
	}
}