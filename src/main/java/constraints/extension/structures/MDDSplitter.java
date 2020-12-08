/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension.structures;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import constraints.extension.structures.MDD.MDDNode;

public class MDDSplitter {

	// private MDD mdd;

	private int[] splitMode;

	private int[][][] splitTuples;

	private Set<int[]>[] splitSets; // used during collecting tuples

	private Map<Integer, Integer>[] auxiliaryLevelMaps;

	public int[] getSplitMode() {
		return splitMode;
	}

	public int[][] getSplitTuples(int i) {
		return splitTuples[i];
	}

	public int getNbAuxiliaryValues(int splitLevel) {
		return auxiliaryLevelMaps[splitLevel].size();
	}

	MDDSplitter(MDD mdd, int[] initialSplitMode) {
		// this.mdd = mdd;
		this.splitMode = initialSplitMode;
		// assert Kit.sum(initialSplitMode) == mdd.firstRegisteredCtr().scp.length;
		for (int i = 0; i < splitMode.length; i++)
			if (i == 0 || i == splitMode.length - 1)
				splitMode[i] += 1; // because one additional variable
			else
				splitMode[i] += 2; // because two additional variables

		splitSets = IntStream.range(0, initialSplitMode.length).mapToObj(i -> new TreeSet<>(Utilities.lexComparatorInt)).toArray(Set[]::new);
		auxiliaryLevelMaps = IntStream.range(0, initialSplitMode.length - 1).mapToObj(i -> new HashMap<>()).toArray(Map[]::new);

		split2(mdd.root, 0);
		splitTuples = new int[splitSets.length][][];
		for (int i = 0; i < splitTuples.length; i++) {
			splitTuples[i] = splitSets[i].toArray(new int[splitSets[i].size()][]);
			splitSets[i].clear();
			splitSets[i] = null;
		}

		for (int i = 0; i < splitTuples.length; i++) {
			System.out.println("i=" + i + " size=" + splitTuples[i].length);
			// for (int[] t : splitTuples[i])
			// System.out.println(Toolkit.buildStringFromInts(t));
		}

		// for (int i = 0; i < splitSets.length; i++) {
		// System.out.println("i=" + i + " size=" + splitSets[i].size());
		// for (int[] t : splitSets[i])
		// System.out.println(Toolkit.buildStringFromInts(t));
		// }
	}

	private int getAuxiliaryLevelNodeId(int nodeId, int splitLevel) {
		return auxiliaryLevelMaps[splitLevel].computeIfAbsent(nodeId, k -> auxiliaryLevelMaps[splitLevel].size());
		// Integer i = auxiliaryLevelMaps[splitLevel].get(nodeId);
		// if (i == null) {
		// int res = auxiliaryLevelMaps[splitLevel].size();
		// auxiliaryLevelMaps[splitLevel].put(nodeId, res);
		// return res;
		//
		// } else
		// return i;
	}

	public void split2(MDDNode startingNode, int splitLevel) {
		int[] currentTuple = new int[splitMode[splitLevel]];
		int currentLevel = 0;
		if (splitLevel > 0)
			currentTuple[currentLevel++] = getAuxiliaryLevelNodeId(startingNode.id, splitLevel - 1);
		getTuples(startingNode, splitLevel, currentTuple, currentLevel, (splitLevel == splitSets.length - 1 ? -1 : splitMode[splitLevel] - 1));
	}

	private void getTuples(MDDNode node, int splitLevel, int[] currentTuple, int currentLevel, int stoppingLevel) {
		if (node == MDDNode.nodeF)
			return;
		if (stoppingLevel == -1) {
			if (node == MDDNode.nodeT)
				splitSets[splitLevel].add(currentTuple.clone());
			else
				for (int i = 0; i < node.sons.length; i++) {
					currentTuple[currentLevel] = i;
					getTuples(node.sons[i], splitLevel, currentTuple, currentLevel + 1, stoppingLevel);
				}
		} else {
			assert node != MDDNode.nodeT && stoppingLevel != -1;
			if (currentLevel == stoppingLevel) {
				currentTuple[currentLevel] = getAuxiliaryLevelNodeId(node.id, splitLevel);
				splitSets[splitLevel].add(currentTuple.clone());

				// System.out.println("splitLevel = " + splitLevel + "currentLevel=" + currentLevel);
				split2(node, splitLevel + 1);
			} else
				for (int i = 0; i < node.sons.length; i++) {
					currentTuple[currentLevel] = i;
					getTuples(node.sons[i], splitLevel, currentTuple, currentLevel + 1, stoppingLevel);
				}
		}
	}
}
