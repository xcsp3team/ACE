/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension.structures;

import constraints.Constraint;
import utility.Kit;
import utility.exceptions.UnreachableCodeException;

/**
 * This class denote any constraint defined in extension. All supports (allowed tuples) or all conflicts (disallowed tuples) are recorded in a list. Note that
 * tuples are recorded as indexes (of values).
 */
public class TableSmart extends ExtensionStructureHard {

	/** The set of smart rows (composed of one tuple and several restrictions). */
	public final SmartTuple[] smartTuples;

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		throw new UnreachableCodeException();
	}

	public TableSmart(Constraint c, SmartTuple[] smartTuples) {
		super(c);
		this.smartTuples = smartTuples;
	}

	@Override
	public boolean checkIdxs(int[] t) {
		for (SmartTuple smartTuple : smartTuples)
			if (smartTuple.contains(t))
				return true;
		return false;
	}

	@Override
	public String toString() {
		return "Smart Tuples : " + Kit.join(smartTuples);
	}

}
