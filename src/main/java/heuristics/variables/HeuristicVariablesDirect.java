/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics.variables;

import search.backtrack.SolverBacktrack;
import utility.exceptions.UnreachableCodeException;
import variables.Variable;

public abstract class HeuristicVariablesDirect extends HeuristicVariables {

	public HeuristicVariablesDirect(SolverBacktrack solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
	}

	@Override
	public double scoreOf(Variable x) {
		throw new UnreachableCodeException("The variable must be directly selected without any iteration");
	}

}
