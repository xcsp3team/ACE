/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACUnguaranteed;
import problem.Problem;
import utility.Kit;
import utility.sets.SetSparse;
import utility.sets.SetSparseReversible;
import variables.Variable;
import variables.domains.Domain;

/**
 * This class establishes that the values assigned to the involved variables of the constraint must be all different.
 */
public final class AllDifferentCounting extends AllDifferentAbstract
		implements TagGACUnguaranteed, TagFilteringCompleteAtEachCall, ObserverBacktrackingSystematic {

	@Override
	public void restoreBefore(int depth) {
		unfixedVars.restoreLimitAtLevel(depth);
	}

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		unfixedVars = new SetSparseReversible(scp.length, pb.variables.length + 1);
	}

	private SetSparse[] sets;
	private SetSparse workingDomSet;
	private SetSparse workingVarSet;
	private SetSparse encounteredSizes;

	private SetSparseReversible unfixedVars;

	public AllDifferentCounting(Problem pb, Variable[] scp) {
		super(pb, scp);
		Kit.control(Variable.haveAllSameDomainType(scp) && scp[0].dom.initSize() < 1000); // current use restrictions
		sets = SetSparse.factoryArray(scp.length, scp[0].dom.initSize() + 1);
		workingDomSet = new SetSparse(scp[0].dom.initSize());
		workingVarSet = new SetSparse(scp.length);
		encounteredSizes = new SetSparse(scp[0].dom.initSize() + 1);
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		for (int i = 0; i < encounteredSizes.size(); i++)
			sets[encounteredSizes.dense[i]].clear();
		Kit.control(Stream.of(sets).allMatch(s -> s.isEmpty())); // TODO to be changed in assert
		encounteredSizes.clear();

		// we first filter future (i.e., non explicitly assigned) variables wrt new fixed (i.e., domain-singleton) variables
		for (int i = unfixedVars.limit; i >= 0; i--) {
			int p = unfixedVars.dense[i];
			if (scp[p].dom.size() > 1)
				continue;
			Variable x = scp[p];
			int v = x.dom.uniqueValue();
			for (int j = futvars.limit; j >= 0; j--) {
				Variable y = scp[futvars.dense[j]];
				if (y != x && y.dom.removeValue(v, false) == false)
					return false;
			}
			unfixedVars.remove(p, pb.solver.depth());
		}

		// sort variables
		for (int i = unfixedVars.limit; i >= 0; i--) {
			int p = unfixedVars.dense[i];
			sets[scp[p].dom.size()].add(p);
			encounteredSizes.add(scp[p].dom.size());
		}
		Kit.control(sets[0].isEmpty());

		for (int i = sets[1].limit; i >= 0; i--) { // TODO try to manage all new fixed variables
			int vapFixed = sets[1].dense[i];
			Variable varFixed = scp[vapFixed];
			int valFixed = varFixed.dom.uniqueValue();
			for (int j = futvars.limit; j >= 0; j--) {
				Variable var = scp[futvars.dense[j]];
				if (var == varFixed)
					continue;
				if (!var.dom.removeValue(valFixed, false))
					return false;
			}
			unfixedVars.remove(vapFixed, pb.solver.depth());
		}
		workingDomSet.clear();
		workingVarSet.clear();
		// displaySizes();

		// for (int i = 0; i < sets[2].getSize(); i++) {
		// int vapi = sets[2].get(i);
		// int idx1 = scp[vapi].dom.getFirstIdx();
		// int idx2 = scp[vapi].dom.getLastIdx();
		// for (int j = i + 1; j < sets[2].getSize(); j++) {
		// int vapj = sets[2].get(j);
		// Domain domy = scp[vapj].dom;
		// if (domy.isPresentIdx(idx1) && domy.isPresentIdx(idx2)) {
		// for (int k = unfixedVariables.getLimit(); k >= 0; k--) {
		// int vap = unfixedVariables.get(k);
		// if (vap != vapi && vap != vapj)
		// if (scp[vap].dom.removeIdx(idx1, false) == false || scp[vap].dom.removeIdx(idx2, false) == false)
		// return false;
		//
		// }
		//
		// }
		//
		// }
		// }
		for (int i = 2; i < sets.length; i++) { // traversal to be improved TODO
			for (int j = sets[i].limit; j >= 0; j--) {
				int vap = sets[i].dense[j];
				workingVarSet.add(vap);
				Domain dom = scp[vap].dom;

				for (int idx = dom.first(); idx != -1; idx = dom.next(idx)) {
					// Kit.prn("idx=" +idx);
					workingDomSet.add(idx);
				}

				if (workingDomSet.size() < workingVarSet.size())
					return false;
				if (workingDomSet.size() == workingVarSet.size()) {
					for (int k = workingVarSet.limit + 1; k < workingVarSet.capacity(); k++)
						if (scp[workingVarSet.dense[k]].dom.remove(workingDomSet, true) == false)
							return false;
				}
				if (workingDomSet.size() > unfixedVars.size())
					return true;
			}
		}
		return true;
	}

	void displaySizes() {
		String s = IntStream.range(2, sets.length).filter(i -> sets[i].size() != 0).mapToObj(i -> i + ":" + sets[i].size()).collect(Collectors.joining(" "));
		Kit.log.info(s);
	}
}
