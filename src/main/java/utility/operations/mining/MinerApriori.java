package utility.operations.mining;

import java.util.ArrayList;
import java.util.List;

import utility.Kit;

public class MinerApriori extends Miner {

	private int minimalItemSize = 1;

	private boolean isMatching(int[] item, int[] tuple) {
		for (int v : item)
			if (tuple[combinator.leftValueIn(v)] != combinator.rightValueIn(v))
				return false;
		return true;
	}

	private int[][] selectFrequentItemsFrom(int[][] currentItems, int[][] tuples) {
		List<int[]> frequentItems = new ArrayList<>(); // the frequent candidates for the current itemset
		for (int[] item : currentItems) {
			int nbOccurrences = 0;
			for (int[] tuple : tuples)
				if (isMatching(item, tuple))
					nbOccurrences++;
			if ((nbOccurrences / (double) (tuples.length)) >= minSup)
				frequentItems.add(item);
		}
		return Kit.intArray2D(frequentItems);
	}

	private boolean isVariableInvolvedIn(int variablePosition, int[] item) {
		for (int v : item)
			if (combinator.leftValueIn(v) == variablePosition)
				return true;
		return false;
	}

	private int[][] createNewItemsFrom(int[][] items) {
		// by construction, all existing currItems have the same size
		int newItemSize = items[0].length + 1;
		List<int[]> newItems = new ArrayList<>();
		// compare each pair of items of size n-1
		for (int i = 0; i < items.length; i++)
			for (int j = i + 1; j < items.length; j++)
				for (int v : items[j]) {
					if (!isVariableInvolvedIn(combinator.leftValueIn(v), items[i])) {
						int[] newItem = new int[newItemSize];
						System.arraycopy(items[i], 0, newItem, 0, newItem.length - 1);
						newItem[newItem.length - 1] = v; // we put the missing value at the end
						newItems.add(newItem);
					}
				}
		return Kit.intArray2D(newItems);
	}

	private int[][] selectFrequentItems(int[] domainSizes, int[][] tuples) {
		List<int[]> selectedItems = new ArrayList<>();
		// building Items of Size1
		int[][] currentItems = new int[(int)Kit.sum(domainSizes)][1];
		for (int i = 0, cnt = 0; i < domainSizes.length; i++)
			for (int j = 0; j < domainSizes[i]; j++)
				currentItems[cnt++][0] = combinator.combinedIntValueFor(i, j);
		// select and iterate building new items (of size increased by 1)
		while (currentItems.length >= 1 && currentItems[0].length < domainSizes.length) {
			currentItems = selectFrequentItemsFrom(currentItems, tuples);
			if (currentItems.length > 0) {
				if (currentItems[0].length >= minimalItemSize)
					for (int[] item : currentItems)
						selectedItems.add(item);
				currentItems = createNewItemsFrom(currentItems);
			}
		}
		return Kit.intArray2D(selectedItems);
	}

	public MinerApriori(int[] domainSizes, int[][] tuples, double minSup) {
		super(domainSizes, minSup);
		this.selectedItems = selectFrequentItems(domainSizes, tuples);
	}
}