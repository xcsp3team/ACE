/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.structures.forSac;

import java.util.stream.IntStream;

import search.Solver;
import variables.Variable;

public class BranchExtended extends Branch {
	public final InferenceUnit[] inferenceUnits;

	private boolean modified;

	private boolean inconsistent;

	public boolean isModified() {
		return modified;
	}

	public boolean isInconsistent() {
		return inconsistent;
	}

	public BranchExtended(Solver solver) {
		super(solver);
		inferenceUnits = new InferenceUnit[solver.pb.variables.length];
	}

	public void recordProblemDomain() {
		for (Variable x : solver.pb.variables) {
			assert x.dom.size() > 0;
			if (x.isAssigned())
				continue;
			if (inferenceUnits[x.num] == null)
				inferenceUnits[x.num] = new InferenceUnit(x.dom.initSize());
			inferenceUnits[x.num].copy(x.dom);
		}
		modified = false;
		assert controlModified();
	}

	public void updateAfterRemovalOf(Variable x, int a) {
		if (has(x)) {
			if (idxs[positions[x.num]] == a) {
				modified = true;
				inconsistent = true;
			}
		} else if (!inferenceUnits[x.num].absents[a]) {
			inferenceUnits[x.num].addAbsent(a);
			modified = true;
		}
		assert controlModified();
	}

	@Override
	public void clear() {
		super.clear();
		for (int i = 0; i < inferenceUnits.length; i++)
			if (inferenceUnits[i] != null)
				inferenceUnits[i].modified = false;
		modified = false;
		inconsistent = false;
	}

	public boolean controlModified() {
		boolean b = IntStream.range(0, inferenceUnits.length).anyMatch(i -> positions[i] == -1 && inferenceUnits[i] != null && inferenceUnits[i].modified);
		if (b && !modified)
			System.out.println("modified = " + modified + " b= " + b);
		return !b || modified;
	}
}