/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class Cutstock implements ProblemAPI {
	int nPieces, pieceLength;
	Item[] items;

	class Item {
		int length, demand;
	}

	@Override
	public void model() {
		int nItems = items.length;
		int[] itemLengths = valuesFrom(items, item -> item.length);

		Var[] p = array("p", size(nPieces), dom(0, 1), "p[i] is 1 iff the ith piece of the stock is used");
		Var[][] r = array("r", size(nPieces, nItems), (i, j) -> dom(range(items[j].demand + 1)),
				"r[i][j] is the number of items of type j built using stock piece i");

		forall(range(nItems), i -> sum(columnOf(r, i), EQ, items[i].demand)).note("each item demand must be exactly satisfied");
		forall(range(nPieces), i -> sum(vars(r[i], p[i]), weightedBy(vals(itemLengths, -pieceLength)), LE, 0))
				.note("each piece of the stock cannot provide more than its length");

		block(() -> {
			decreasing(p);
			decreasing(r);
		}).tag(SYMMETRY_BREAKING);

		// annotateVarhStatic(p);

		minimize(SUM, p).note("minimizing the number of used pieces");
	}
}
