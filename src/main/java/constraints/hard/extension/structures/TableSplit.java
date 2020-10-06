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
 * This class denote any constraint defined in extension. All supports (allowed tuples) or all conflicts (disallowed tuples) are recorded in a list.
 * Note that tuples are recorded as indexes (of values).
 */
public class TableSplit extends ExtensionStructureHard {

	public final SegmentedTuple[] splitTuples;

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		throw new UnreachableCodeException();
	}

	public TableSplit(Constraint c, SegmentedTuple[] splitTuples) {
		super(c);
		this.splitTuples = splitTuples;
	}

	@Override
	public boolean checkIdxs(int[] t) {
		for (SegmentedTuple splitTuple : splitTuples)
			if (splitTuple.contains(t))
				return true;
		return false;
	}

	@Override
	public String toString() {
		return "Split Tuples : " + Kit.join(splitTuples);
	}

}
