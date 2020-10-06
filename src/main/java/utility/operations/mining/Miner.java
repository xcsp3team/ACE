package utility.operations.mining;

import utility.Kit;
import utility.operations.CombinatorOfTwoInts;

public class Miner {

	public final CombinatorOfTwoInts combinator;

	protected int[][] selectedItems;

	protected double minSup; // minimum support for a frequent itemset in percentage, e.g. 0.8

	public int[][] getSelectedItems() {
		return selectedItems;
	}

	public Miner(int[] domainSizes, double minSup) {
		this.minSup = minSup;
		this.combinator = new CombinatorOfTwoInts(domainSizes.length - 1, Kit.computeMaxOf(domainSizes));
		Kit.control(minSup > 0 && minSup < 1);
	}

}