/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.Set;
import java.util.TreeSet;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.global.AllDifferent.AllDifferentComplete;
import problem.Problem;
import sets.SetSparse;
import variables.Variable;

public final class Circuit extends AllDifferentComplete {

	@Override
	public boolean checkValues(int[] t) {
		if (super.checkValues(t) == false)
			return false;
		int nLoops = (int) IntStream.range(0, t.length).filter(i -> t[i] == i).count();
		if (nLoops == t.length)
			return false; // no circuit at all
		int i = 0;
		while (i < scp.length && t[i] == i)
			i++;
		Set<Integer> s = new TreeSet<>();
		while (t[i] != i && !s.contains(t[i])) {
			s.add(t[i]);
			i = t[i];
		}
		return s.size() == (t.length - nLoops);
	}

	private SetSparse set;

	public Circuit(Problem pb, Variable[] scp) {
		super(pb, scp);
		this.set = new SetSparse(scp.length);
		control(Stream.of(scp).allMatch(x -> x.dom.areInitValuesSubsetOf(pb.api.range(scp.length))));
	}

	@Override
	public boolean isGuaranteedAC() {
		return false;
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (super.runPropagator(x) == false)
			return false;
		int minimalCircuitLength = 0;
		for (int i = 0; i < scp.length; i++)
			if (scp[i].dom.containsValue(i) == false)
				minimalCircuitLength++;
		for (int i = 0; i < scp.length; i++) {
			if (scp[i].dom.size() == 1) {
				int j = scp[i].dom.singleValue();
				if (i == j)
					continue; // because self-loop
				set.clear();
				set.add(i); // i belongs to the circuit
				if (scp[j].dom.removeValueIfPresent(j) == false) // because self-loop not possible for j
					return false;
				while (set.size() + 1 < minimalCircuitLength) {
					if (scp[j].dom.removeValuesIn(set) == false)
						return false; // because we cannot close the circuit now (it would be too short)
					if (scp[j].dom.size() == 1) {
						if (set.isPresent(j))
							return false; // because two times the same value
						set.add(j); // j belongs to the circuit
						j = scp[j].dom.singleValue(); // we know for sure here that the *new value of j* is different from the previous one
						if (scp[j].dom.removeValueIfPresent(j) == false) // because self-loop not possible for j
							return false;
					} else
						break;
				}
			}
		}
		return true;
	}

}
