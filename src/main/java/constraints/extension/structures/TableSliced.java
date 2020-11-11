/**
 *  AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 *  All rights reserved. 
 *  
 *  This program and the accompanying materials are made 
 *  available under the terms of the CONTRAT DE LICENCE 
 *  DE LOGICIEL LIBRE CeCILL which accompanies this distribution, 
 *  and is available at http://www.cecill.info
 */
package constraints.extension.structures;

import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.List;

import constraints.Constraint;
import dashboard.ControlPanel;
import problem.ProblemStuff.Repartitioner;
import utility.Kit;
import utility.Kit.Stopwatch;
import utility.operations.CombinatorOfTwoInts;
import utility.operations.Miner;
import utility.operations.Miner.MinerApriori;
import utility.operations.Miner.MinerFPTree;
import variables.Variable;

/**
 * This class denote any constraint defined in extension. All supports (allowed tuples) or all conflicts (disallowed tuples) are recorded in a list.
 * Note that tuples are recorded as indexes (of values).
 */
public class TableSliced extends Table {

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/

	private final static DecimalFormat df = new DecimalFormat("####.##");

	public static long totalInitialSpace, totalReducedSpace;

	public static Stopwatch stopwatch;

	public static long wck;

	/**********************************************************************************************
	 * Intern class Slice
	 *********************************************************************************************/

	public class Slice {
		public int id;
		public int[] itemVariablePositions;
		public int[] itemIndexes;
		public int[] subtableVariablePositions;
		// public int[][] subtable;
		public byte[][] subtable;

		private void setItemAndSubtable(int[] item, List<int[]> matchingTuples) {
			// setting itemVariablePositions and itemIndexes
			itemVariablePositions = new int[item.length];
			itemIndexes = new int[item.length];
			for (int i = 0; i < item.length; i++) {
				itemVariablePositions[i] = combinator.leftValueIn(item[i]);
				itemIndexes[i] = combinator.rightValueIn(item[i]);
			}
			assert Kit.isIncreasing(itemVariablePositions);
			// setting tableVariablePositions and table
			int tableArity = matchingTuples.get(0).length - item.length;
			subtableVariablePositions = new int[tableArity];
			for (int i = 0, j = 0, pos = 0; i < subtableVariablePositions.length;) {
				while (j < itemVariablePositions.length && pos == itemVariablePositions[j]) {
					pos++;
					j++;
				}
				subtableVariablePositions[i++] = pos++;
			}
			// Kit.prn(" control pos " + Kit.implode(itemVariablePositions) + " -- " + Kit.implode(tableVariablePositions));
			subtable = new byte[matchingTuples.size()][subtableVariablePositions.length];
			// subtable = new int[matchingTuples.size()][subtableVariablePositions.length];
			int i = 0;
			for (int[] matchingTuple : matchingTuples) {
				for (int j = 0; j < subtableVariablePositions.length; j++)
					subtable[i][j] = (byte) matchingTuple[subtableVariablePositions[j]];
				// subtable[i][j] = matchingTuple[subtableVariablePositions[j]];
				i++;
			}
			// Kit.prn(this);
		}

		private Slice(int id, int[] item, List<int[]> matchingTuples) {
			this.id = id;
			setItemAndSubtable(item, matchingTuples);
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder(" Item : " + Kit.join(itemVariablePositions) + " = " + Kit.join(itemIndexes));
			sb.append("\nsubtable :\n " + Kit.join(subtableVariablePositions) + "\n" + subtable.length + "\n");
			return sb.toString();
		}
	}

	/**********************************************************************************************
	 * Fields and Methods
	 *********************************************************************************************/

	private final int minimalSubtableSize = 10;

	private CombinatorOfTwoInts combinator;

	public Slice[] slices;

	private boolean isMatching(int[] item, int[] tuple) {
		for (int v : item)
			if (tuple[combinator.leftValueIn(v)] != combinator.rightValueIn(v))
				return false;
		return true;
	}

	private Slice buildRemainingSlice(int id, int[][] tuples, int currLimit) {
		if (currLimit == -1)
			return null;
		List<int[]> matchingTuples = new ArrayList<>();
		for (int i = 0; i <= currLimit; i++)
			matchingTuples.add(tuples[i]);
		return new Slice(id, new int[0], matchingTuples);
	}

	private Slice[] buildSlicesFrom(int[][] selectedItems) {
		// Kit.prn(" Final Selected items: " + selectedItems.length);
		int[][] tuples = Kit.cloneDeeply(this.tuples);
		int currLimit = tuples.length - 1;
		List<Slice> listOfSlices = new ArrayList<>();
		List<int[]> matchingTuples;
		int[] tuplesToBeRestored = new int[minimalSubtableSize - 1];
		for (int i = selectedItems.length - 1; i >= 0; i--) {
			matchingTuples = new ArrayList<>();
			for (int j = 0; j <= currLimit;)
				if (isMatching(selectedItems[i], tuples[j])) {
					matchingTuples.add(tuples[j]);
					if (matchingTuples.size() < tuplesToBeRestored.length)
						tuplesToBeRestored[matchingTuples.size() - 1] = j;
					tuples[j] = tuples[currLimit--];
				} else
					j++;
			if (matchingTuples.size() >= minimalSubtableSize) {
				Kit.sort(selectedItems[i]);
				listOfSlices.add(new Slice(listOfSlices.size(), selectedItems[i], matchingTuples));
			} else {
				for (int j = matchingTuples.size() - 1; j >= 0; j--) {
					tuples[tuplesToBeRestored[j]] = matchingTuples.get(j);
					currLimit++;
				}
			}
		}
		// define the remaining piece
		Slice remainingSlice = buildRemainingSlice(listOfSlices.size(), tuples, currLimit);
		if (remainingSlice != null)
			listOfSlices.add(remainingSlice);
		return listOfSlices.toArray(new Slice[listOfSlices.size()]);
	}

	private void displayStatistics() {
		Repartitioner<Integer> subtableSizes = new Repartitioner<Integer>(), itemSizes = new Repartitioner<Integer>();
		long initialSpace = tuples.length * tuples[0].length, reducedSpace = 0;
		for (Slice piece : slices) {
			reducedSpace += piece.itemVariablePositions.length + (piece.subtable.length * piece.subtableVariablePositions.length);
			subtableSizes.add(piece.subtable.length);
			itemSizes.add(piece.itemVariablePositions.length);
		}
		Kit.log.info("nbTuples=" + tuples.length + " initialSpace=" + initialSpace + " reducedSpace=" + reducedSpace + " compressionFactor="
				+ df.format(initialSpace / (double) reducedSpace));
		Kit.log.info("nbPieces=" + slices.length + " items=" + itemSizes + " subtables=" + subtableSizes + "\n");
		totalInitialSpace += initialSpace;
		totalReducedSpace += reducedSpace;
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		super.storeTuples(tuples, positive);
		ControlPanel cfg = firstRegisteredCtr().pb.rs.cp;
		if (stopwatch == null)
			stopwatch = new Stopwatch();
		stopwatch.start();
		int[] domainSizes = Variable.domSizeArrayOf(firstRegisteredCtr().scp, true);
		Miner miner = cfg.settingExtension.miningApriori ? new MinerApriori(domainSizes, tuples, cfg.settingExtension.miningThreshold)
				: new MinerFPTree(domainSizes, tuples, cfg.settingExtension.miningThreshold);
		this.combinator = miner.combinator;
		this.slices = buildSlicesFrom(miner.getSelectedItems());
		wck += stopwatch.getWckTime();
		displayStatistics();
	}

	public TableSliced(Constraint ctr) {
		super(ctr);
	}
}
