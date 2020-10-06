/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.math.BigDecimal;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

// 63 on CSPLib
public class Auction implements ProblemAPI {

	Bid[] bids;

	class Bid {
		String value;
		int[] items;
	}

	private int[] bidValues() {
		BigDecimal[] t = Stream.of(bids).map(b -> new BigDecimal(b.value).stripTrailingZeros()).toArray(BigDecimal[]::new);
		int maxScale = Stream.of(t).filter(s -> s.scale() > 0).mapToInt(s -> s.scale()).max().orElse(0);
		return valuesFrom(t, b -> b.movePointRight(maxScale).intValueExact());
	}

	@Override
	public void model() {
		int[] allItems = singleValuesFrom(bids, bid -> bid.items);
		int nBids = bids.length, nItems = allItems.length;

		Var[] b = array("b", size(nBids), dom(0, 1), "b[i] is 1 iff the ith bid is selected");

		forall(range(nItems), i -> {
			int[] itemBids = select(range(nBids), j -> contains(bids[j].items, allItems[i]));
			if (itemBids.length > 1)
				atMost1(select(b, itemBids), takingValue(1));
		}).note("avoiding intersection of bids");

		maximize(SUM, b, weightedBy(bidValues())).note("maximizing summed value of selected bids");
	}
}

// private int[] allItems() {
// return Stream.of(bids).map(b -> IntStream.of(b.items)).flatMapToInt(i -> i).sorted().distinct().toArray();
// }

// private int[][] itemMemberships() {
// Map<Integer, List<Integer>> map = new TreeMap<>();
// for (int i = 0; i < bids.length; i++)
// for (int item : bids[i].items) {
// List<Integer> list = map.getOrDefault(item, new ArrayList<>());
// list.add(i);
// map.put(item, list);
// }
// Stream<List<Integer>> relevantItems = map.values().stream().filter(l -> l.size() > 1);
// return relevantItems.map(l -> l.stream().mapToInt(i -> i).toArray()).toArray(int[][]::new);
// }

// private int[] allItems() {
// return IntStream.range(0, bids.length).flatMap(i -> IntStream.of(bids[i].items)).sorted().distinct().toArray();
// }