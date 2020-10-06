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

public class Knapsack implements ProblemAPI {
	int capacity;
	Item[] items;

	class Item {
		int weight, value;
	}

	@Override
	public void model() {
		int nItems = items.length;
		int[] weights = valuesFrom(items, i -> i.weight), values = valuesFrom(items, i -> i.value);

		Var[] x = array("x", size(nItems), dom(0, 1), "x[i] is 1 iff the ith item is selected");

		sum(x, weightedBy(weights), LE, capacity);
		maximize(SUM, x, weightedBy(values)).note("maximizing summed up value (benefit)");

		// IntStream.range(0, nItems).forEach(i -> x[i].data = items[i].value / (double) items[i].weight); // to be used here by the
		// specific var // heuristic called Data
	}
}
