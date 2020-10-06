/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import problem.Problem;
import variables.Variable;

public class AllDifferent extends AllDifferentAbstract implements ObserverBacktrackingSystematic, TagGACGuaranteed, TagFilteringCompleteAtEachCall {

	@Override
	public void restoreBefore(int depth) {
		matcher.restoreAtDepthBefore(depth);
	}

	private Matcher matcher;

	public AllDifferent(Problem pb, Variable[] scp) {
		super(pb, scp);
		this.matcher = new MatcherAllDifferent(this);
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (matcher.findMaximumMatching() == false)
			return x.dom.fail();
		matcher.removeInconsistentValues(); // no more possible failure at this step
		return true;
	}
}
