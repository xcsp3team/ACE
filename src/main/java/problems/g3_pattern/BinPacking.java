package problems.g3_pattern;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

import problem.Problem;
import utility.Kit;

// optimum 5 for Scholl/skj1/n1c1w4a.txt
public class BinPacking implements ProblemAPI {
	static final int NO = 0;

	int binCapacity;
	int[] itemWeights;

	private int[] occWeights(int length) {
		int[] occWeights = new int[length];
		occWeights[0] = 1;
		for (int i = 1, currentWeight = 0; i < itemWeights.length; i++) {
			if (itemWeights[i] != itemWeights[i - 1])
				currentWeight++;
			occWeights[currentWeight]++;
		}
		return occWeights;
	}

	private int nBins() {
		int nBins = 0;
		for (int i = 0, currentBinLoad = 0; i < itemWeights.length; i++) {
			currentBinLoad += itemWeights[i];
			if (currentBinLoad > binCapacity) {
				nBins++;
				currentBinLoad = itemWeights[i];
			}
		}
		return nBins;
	}

	private int nMaxItemsPerBin() {
		for (int i = 0, sum = 0; i < itemWeights.length; i++) {
			sum += itemWeights[i];
			if (sum > binCapacity) {
				return i;
			}
		}
		return -1;
	}

	@Override
	public void model() {
		int[] distinctWeights = singleValuesIn(itemWeights);
		int[] occWeights = occWeights(distinctWeights.length);
		int nBins = nBins(), nMaxItemsPerBin = nMaxItemsPerBin();

		// Var u = var("u", dom(range(nBins + 1)), "u is the number of unused bins");
		Var[][] w = array("w", size(nBins, nMaxItemsPerBin), dom(vals(NO, distinctWeights)),
				"w[i][j] indicates the weight of the jth object put in the ith bin. It is 0 if there is no object at this place.");

		if (modelVariant("")) {
			forall(range(nBins), i -> sum(w[i], LE, binCapacity)).note("not exceeding the capacity of each bin");
			forall(range(nBins), i -> decreasing(w[i])).note("items are stored decreasingly in each bin according to their weights");
		} else if (modelVariant("table")) {
			Table table = buildTable(nMaxItemsPerBin);
			// forall(range(nBins), i -> extension(b[i], table, Option.TO_MDD)); // , Option.KEY("k")));
			forall(range(nBins), i -> extension(w[i], table));
		} else if (modelVariant("mdd")) {
			// forall(range(nBins), i -> sumKnapsack(b[i], 0, binCapacity));
			// forall(range(nBins), i -> ordered(b[i], GE));
			Table table = buildTable(nMaxItemsPerBin);
			forall(range(nBins), i -> ((Problem) imp()).mdd(w[i], table.toArray()));
		}
		// cardinality(vars(b), distinctWeights, occWeights);
		cardinality(vars(w), vals(NO, distinctWeights), occurExactly(vals(nBins * nMaxItemsPerBin - itemWeights.length, occWeights)))
				.note("ensuring that each item is stored in a bin");
		decreasing(w).tag(SYMMETRY_BREAKING);

		// exactly(columnOf(w, 0), NO, u).note("counting the number of unused bins");
		maximize(SUM, treesFrom(range(nBins), i -> eq(w[i][0], 0))).note("maximizing the number of unused bins");
	}

	private boolean recursiveBuild(Table table, int nbStored, int[] tmp, int i, int sum) {
		if (table.size() > 200000000)
			return false;
		assert sum + itemWeights[i] <= binCapacity;
		tmp[nbStored++] = itemWeights[i];
		sum += itemWeights[i];
		int[] tmp2 = tmp.clone();
		for (int j = nbStored; j < tmp2.length; j++)
			tmp2[j] = 0;
		table.add(tmp2);
		for (int j = 0; j < i; j++) {
			if (sum + itemWeights[j] > binCapacity)
				break;
			if (j < i - 1 && itemWeights[j] == itemWeights[j + 1])
				continue;
			if (!recursiveBuild(table, nbStored, tmp, j, sum))
				return false;
		}
		return true;
	}

	private Table build(int nMaxItemsPerBin) {
		Table table = new Table();
		int[] tmp = new int[nMaxItemsPerBin];
		table.add(tmp.clone()); // all 0
		for (int i = 0; i < itemWeights.length; i++) {
			if (i < itemWeights.length - 1 && itemWeights[i] == itemWeights[i + 1])
				continue;
			if (!recursiveBuild(table, 0, tmp, i, 0))
				Kit.exit("not possible to build the table with less than the specified number of tuples");
		}
		return table;
	}

	private Table buildTable(int nMaxItemsPerBin) {
		return build(nMaxItemsPerBin); // PossibleBinContents();
		// System.out.println(Kit.join(table));
		// if (table == null)
		// Kit.exit("not possible to build the table with less than the specified number of tuples");
		// return table;
	}

	// private int[][] buildPossibleBinContents() {
	// list = new ArrayList<int[]>();
	// // if (framework == EFramework.COP)
	// list.add(Kit.repeat(NO, nMaxItemsPerBin));
	// int[] tmp = new int[nMaxItemsPerBin];
	// for (int i = 0; i < itemWeights.length; i++) {
	// System.out.println("i=" + i);
	// // if (i > 0 && itemWeights[i] == itemWeights[i - 1])
	// // continue;
	// tmp[0] = itemWeights[i];
	// if (!f(1, tmp, i + 1, tmp[0], list))
	// return null;
	// }
	//
	// return Kit.intArray2D(list);
	// }
	//
	// private boolean f(int nbStored, int[] tmp, int i, int sum, List<int[]> list) {
	// // System.out.println("calling at pos " + nbStored + " from sum " + sum);
	// if (list.size() > 200000000)
	// return false;
	// if (nbStored == tmp.length) {
	// // if (!isSubsumed(tmp, list)) // Too costly
	// list.add(tmp.clone());
	// } else
	// for (int k = i; k < itemWeights.length; k++)
	// if (sum + itemWeights[k] <= binCapacity) {
	// tmp[nbStored] = itemWeights[k];
	// f(nbStored + 1, tmp, k + 1, sum + itemWeights[k], list);
	// } else {
	// Arrays.fill(tmp, nbStored, tmp.length, NO);
	// // if (!isSubsumed(tmp, list)) // Too costly
	// list.add(tmp.clone());
	// break;
	// }
	// return true;
	// }

	// private boolean isSubsumed(int[] currentTuple, List<int[]> tuples) {
	// for (int[] storedTuple : tuples)
	// if (isSubsumed(currentTuple, storedTuple))
	// return true;
	// return false;
	// }
	//
	// private boolean isSubsumed(int[] currentTuple, int[] storedTuple) {
	// int pos = 0;
	// while (pos < storedTuple.length && storedTuple[pos] != currentTuple[0])
	// pos++;
	// if (pos == storedTuple.length)
	// return false;
	// for (int i = pos + 1; i < storedTuple.length; i++)
	// if (storedTuple[i] != currentTuple[i - pos])
	// return false;
	// if (pos == 0 || currentTuple[currentTuple.length - pos] == NOTHING)
	// return true;
	// return false;
	// }
}
