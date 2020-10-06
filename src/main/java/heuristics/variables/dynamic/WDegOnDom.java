/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics.variables.dynamic;

import constraints.Constraint;
import search.backtrack.SolverBacktrack;
import utility.Enums.EWeighting;
import variables.Variable;

/**
 * This heuristic, called <i>wdeg/dom </i>, selects a (best evaluated) variable by considering the ratio weighted degree to domain size. The weighted
 * degree of a variable X is equal to the sum of the weight of all constraints involving X and at least another future variable. see [Boussemart,
 * Hemery, Lecoutre, Sais, ECAI, 2004].
 */
public class WDegOnDom extends HeuristicVariablesConflictBased {

	public WDegOnDom(SolverBacktrack solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
	}

	@Override
	public double scoreOf(Variable x) {
		if (settings.weighting == EWeighting.CHS) {
			double d = 0;
			for (Constraint c : x.ctrs)
				if (c.futvars.size() > 1)
					d += cscores[c.num];
			return d / x.dom.size();
		}
		return vscores[x.num] / x.dom.size();
	}
}
