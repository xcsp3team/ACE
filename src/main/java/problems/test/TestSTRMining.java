/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import java.util.Arrays;
import java.util.Random;
import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

import utility.Kit;
import utility.operations.Base;

// TODO same possible tuple in two different implics :
public class TestSTRMining implements ProblemAPI {

	int n, d, e, r;
	int itemLength, subtableSize, nSlices, seed, nPigeons;

	void data() {
		n = imp().askInt("Nb variables");
		d = imp().askInt("Nb values");
		e = imp().askInt("Nb constraints");
		r = imp().askInt("Arity");
		itemLength = imp().askInt("Item length");
		subtableSize = imp().askInt("Subtable size");
		nSlices = imp().askInt("Nb slices");
		seed = imp().askInt("Seed");
		nPigeons = imp().askInt("Nb pigeons");
		Kit.control(Math.pow(d, r - itemLength) < Integer.MAX_VALUE);
		Kit.control(subtableSize <= Math.pow(d, r - itemLength), () -> " Bad parameters");
		Kit.control(nSlices <= d);
	}

	private int[] buildTuple(int length, int[] frozenPositions, int[] frozenValues, int[] subtuple) {
		int currFrozenPosition = 0, subtuplePosition = 0;
		int[] t = new int[length];
		for (int i = 0; i < t.length; i++)
			t[i] = currFrozenPosition < frozenPositions.length && i == frozenPositions[currFrozenPosition] ? frozenValues[currFrozenPosition++]
					: subtuple[subtuplePosition++];
		return t;
	}

	private void buildSlice(int id, int[][] tuples, int offset, int commonVariablePositionInItems, Random random) {
		final int[] itemPositions = Kit.pickDifferentValues(itemLength, r, random);
		if (!Kit.isPresent(commonVariablePositionInItems, itemPositions)) {
			int position = random.nextInt(itemLength);
			itemPositions[position] = commonVariablePositionInItems;
			Arrays.sort(itemPositions);
		}
		int[] itemValues = IntStream.range(0, itemLength).map(j -> itemPositions[j] == commonVariablePositionInItems ? id : random.nextInt(d)).toArray();
		Kit.log.info("New slice with prefix " + Kit.join(itemPositions) + " = " + Kit.join(itemValues));
		int[] subtuplesIndexes = Kit.pickDifferentValues(subtableSize, (int) Math.pow(d, r - itemLength), random);
		for (int i = 0; i < subtableSize; i++) {
			tuples[offset + i] = buildTuple(r, itemPositions, itemValues, Base.baseValueFor(subtuplesIndexes[i], r - itemLength, d));
			// Kit.prn(Kit.implode(tuples[offset + i]));
		}
	}

	@Override
	public void model() {
		Random random = new Random(seed);
		int[] commonVariablePositionInItems = IntStream.range(0, e).map(i -> random.nextInt(r)).toArray();

		Var[] x = array("x", size(n), dom(range(d))); // main variables
		Var[] p = array("P", size(nPigeons), dom(range(nPigeons - 1))); // pigeons variables

		forall(range(e), i -> {
			int[] scopeIds = Kit.pickDifferentValues(r, n, random);
			Var[] scope = variablesFrom(scopeIds, id -> x[id]);
			int[][] tuples = new int[nSlices * subtableSize][];
			for (int j = 0; j < nSlices; j++)
				buildSlice(j, tuples, j * subtableSize, commonVariablePositionInItems[i], random);
			Arrays.sort(tuples, Utilities.lexComparatorInt);
			extension(scope, tuples);
		});
		forall(range(nPigeons).range(nPigeons), (i, j) -> {
			if (i < j)
				intension(ne(p[i], p[j]));
		});
	}
}
