/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

// m2s = m2 sans redundancy et symBreaking
// m2s-mini = m2 avec extension instead of intension and no redundancy and symmetry breaking
public class SteelMillSlab implements ProblemAPI {

	int[] slabCapacities;
	Order[] orders;

	class Order {
		int size, color;
	}

	private int[][] colorGroups(int[] allColors) {
		return IntStream.of(allColors).mapToObj(c -> range(orders.length).select(i -> orders[i].color == c)).toArray(int[][]::new);
	}

	@Override
	public void model() {
		// we need sorted slab capacities, and also 0 as capacity
		slabCapacities = singleValuesIn(0, slabCapacities); // IntStream.of(addInt(slabCapacities, 0)).sorted().distinct().toArray();
		int maxCapacity = slabCapacities[slabCapacities.length - 1];
		int[] possibleLosses = range(maxCapacity + 1).map(i -> minOf(select(slabCapacities, v -> v >= i)) - i);

		// int[] possibleLosses = range(maxCapacity + 1).map(i -> IntStream.of(slabCapacities).filter(v -> v >= i).min().getAsInt() - i);
		int[] sizes = valuesFrom(orders, o -> o.size);
		int totalSize = sumOf(sizes);
		int[] allColors = singleValuesFrom(orders, order -> order.color);
		int nOrders = orders.length, nSlabs = orders.length, nColors = allColors.length;

		Var[] sb = array("sb", size(nOrders), dom(range(nSlabs)), "sb[i] is the slab used to produce the ith order");
		Var[] ld = array("ld", size(nSlabs), dom(range(maxCapacity + 1)), "ld[j] is the load of the jth slab");
		Var[] ls = array("ls", size(nSlabs), dom(possibleLosses), "ls[j] is the loss of the jth slab");

		if (modelVariant("")) {
			forall(range(nSlabs), s -> sum(treesFrom(sb, x -> eq(x, s)), weightedBy(sizes), EQ, ld[s])).note("computing (and checking) the load of each slab");
			forall(range(nSlabs), s -> extension(vars(ld[s], ls[s]), indexing(possibleLosses))).note("computing the loss of each slab");
			int[][] colorMemberships = colorGroups(allColors);
			forall(range(nSlabs), s -> sum(Stream.of(colorMemberships).map(g -> or(treesFrom(g, o -> eq(sb[o], s)))), LE, 2))
					.note("no more than two colors for each slab");
		}
		if (modelVariant("01")) {
			Var[][] y = array("y", size(nSlabs, nOrders), dom(0, 1), "y[j][i] is 1 iff the jth slab is used to produce the ith order");
			Var[][] z = array("z", size(nSlabs, nColors), dom(0, 1), "z[j][c] is 1 iff the jth slab is used to produce an order of color c");
			forall(range(nSlabs).range(nOrders), (s, o) -> equivalence(eq(sb[o], s), y[s][o])).note("linking variables sb and y");
			forall(range(nSlabs).range(nOrders), (s, o) -> implication(eq(sb[o], s), z[s][Utilities.indexOf(orders[o].color, allColors)]))
					.note("linking variables sb and z");
			// the reverse side ? eq(z[s]{c] = 1 => or(...) // not really necessary but could help ?
			forall(range(nSlabs), s -> sum(y[s], weightedBy(sizes), EQ, ld[s])).note("computing (and checking) the load of each slab");
			forall(range(nSlabs), s -> extension(vars(ld[s], ls[s]), indexing(possibleLosses))).note("computing the loss of each slab");
			forall(range(nSlabs), s -> sum(z[s], LE, 2)).note("no more than two colors for each slab");
		}

		sum(ld, EQ, totalSize).tag(REDUNDANT_CONSTRAINTS);
		block(() -> {
			decreasing(ld);
			forall(range(nOrders).range(nOrders), (i, j) -> {
				if (i < j && orders[i].size == orders[j].size && orders[i].color == orders[j].color)
					lessEqual(sb[i], sb[j]);
			});
		}).tag(SYMMETRY_BREAKING);

		minimize(SUM, ls).note("minimizing summed up loss");
	}
}

// forall(range(nSlabs), s -> sum(colorGroups.stream().map(g -> or(g.stream().map(o -> eq(sb[o], s)))), LE, 2))
// .note("no more than two colors for each slab");

// forall(range(nSlabs), s -> sum(Stream.of(sb).map(x -> eq(x, s)), sizes, EQ, ld[s])).note("computing (and checking) the load of each
// slab");

// another model with domains defined with all pairs of colors ?

// forall(range(nOrders).range(nOrders).range(nOrders), (i, j, k) -> {
// if (orders[i].color != orders[j].color && orders[i].color != orders[k].color && orders[j].color != orders[k].color)
// notAllEqual(x[i], x[j], x[k]);
// }); // TOO MANY CONSTRAINTS
