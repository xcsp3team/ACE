/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.stream.IntStream;

import constraints.Constraint.CtrGlobal;
import interfaces.Observers.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import sets.SetSparse;
import utility.Kit;
import variables.Variable;

/**
 * This constraint ensures that all values assigned to the variables of its cope are all equal.
 */
public final class AllEqual extends CtrGlobal implements ObserverBacktrackingSystematic, TagGACGuaranteed, TagFilteringCompleteAtEachCall, TagSymmetric {

	@Override
	public final boolean checkValues(int[] t) {
		return IntStream.range(0, t.length - 1).allMatch(i -> t[i] == t[i + 1]);
	}

	@Override
	public void restoreBefore(int depth) {
		if (depth == entailedLevel)
			entailedLevel = -1;
		if (entailedLevel == -1)
			for (int i = scp.length - 1; i >= 0; i--)
				frontier[i] = scp[i].dom.lastRemoved();
	}

	/**
	 * frontier[x.num] stores for any variable x the last removed (index of) value during the last call to runPropagator.
	 */
	private final int[] frontier;

	private final SetSparse set;

	public AllEqual(Problem pb, Variable[] list) {
		super(pb, list);
		control(list.length >= 2 && Variable.haveSameDomainType(list));
		this.frontier = Kit.repeat(-1, list.length);
		this.set = new SetSparse(list[0].dom.initSize());
		// this.vals = new TreeSet<>(); // Hashset is very slow
		defineKey();
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (entailedLevel != -1)
			return true;

		Variable y = x.dom.size() == 1 ? x : Variable.firstSingletonVariableIn(scp); // we look for a variable y with a singleton domain

		if (y != null) { // we remove the unique value from the domains of the future variables
			int a = y.dom.unique();
			for (Variable z : scp)
				if (z.dom.reduceTo(a) == false)
					return false;
			entailedLevel = problem.solver.depth();
			return true;
		}

		// // we collect the set of dropped (indexes of) values (since the last call) over all future variables
		set.clear();
		for (int i = scp.length - 1; i >= 0; i--)
			for (int a = scp[i].dom.lastRemoved(); a != frontier[i]; a = scp[i].dom.prevRemoved(a))
				set.add(a);

		// we remove these dropped (indexes of) values from the domain of all future variables
		for (int i = scp.length - 1; i >= 0; i--) // the other side (0 to scp.length) is very long for Domino (because of the revision ordering heuristic)
			if (scp[i].dom.remove(set, true) == false)
				return false;

		// we record the frontier of dropped (indexes of) values for the next call
		for (int i = scp.length - 1; i >= 0; i--)
			frontier[i] = scp[i].dom.lastRemoved();
		return true;
	}
}

// we collect the set of dropped values (since the last call) over all future variables
// vals.clear();
// for (int i = scp.length - 1; i >= 0; i--) {
// Domain dom = scp[i].dom;
// for (int a = dom.lastRemoved(); a != frontier[i]; a = dom.prevRemoved(a))
// vals.add(dom.toVal(a));
// }
// // System.out.println("ssiii " + vals.size() + " " + (cnt++));
// // // we remove these dropped (indexes of) values from the domain of all future variables
// for (int i = scp.length - 1; i >= 0; i--)
// if (scp[i].dom.removeValuesIn(vals) == false)
// return false;