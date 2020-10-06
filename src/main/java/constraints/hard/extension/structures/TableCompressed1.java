/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension.structures;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import constraints.Constraint;
import utility.Kit;
import utility.Kit.IntArrayHashKey;
import utility.exceptions.MissingImplementationException;
import variables.Variable;

public class TableCompressed1 extends ExtensionStructureHard {
	protected boolean positive;

	protected int[][][] compressedTuples;

	public boolean isPositive() {
		return positive;
	}

	public int[][][] getCompressedTuples() {
		return compressedTuples;
	}

	public int[][] getCompressedTuple(int i) {
		return compressedTuples[i];
	}

	Map<IntArrayHashKey, MDDNode> map;

	private MDDNode rec(MDDNode node) {
		if (node.isLeaf())
			return node;
		MDDNode[] childs = node.sons;
		for (int i = 0; i < childs.length; i++)
			childs[i] = rec(childs[i]);
		int[] t = new int[childs.length];
		for (int i = 0; i < childs.length; i++)
			t[i] = childs[i].id;
		IntArrayHashKey hk = new IntArrayHashKey(t);
		return map.computeIfAbsent(hk, k -> node);
	}

	private void reduce(MDDNode node, int[] previousTuple, int[] currentTuple) {
		int i = 0;
		// MDDNode node = root;
		while (previousTuple[i] == currentTuple[i]) {
			node = node.sons[previousTuple[i]];
			i++;
		}
		// System.out.println(Toolkit.buildStringFromInts(previousTuple) + " " + Toolkit.buildStringFromInts(currentTuple) + " i=" + i);
		node.sons[previousTuple[i]] = rec(node.sons[previousTuple[i]]);
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		Kit.control(positive && tuples.length > 0);

		Constraint ctr = firstRegisteredCtr();
		int[] domainSizes = Variable.domSizeArrayOf(ctr.scp, true);

		map = new HashMap<>(2000);

		int[] previousTuple = null, currentTuple = new int[tuples[0].length];
		MDD mdd = new MDD(null);
		MDDNode root = new MDDNode(mdd, 0, domainSizes[0], positive);
		if (ctr.indexesMatchValues) {
			for (int i = 0; i < tuples.length; i++) {
				currentTuple = tuples[i];
				root.addTuple(currentTuple, positive, domainSizes);
				if (previousTuple == null)
					previousTuple = currentTuple.clone();
				else {
					reduce(root, previousTuple, currentTuple);
					int[] tmp = previousTuple;
					previousTuple = currentTuple;
					currentTuple = tmp;
				}
			}
		} else {
			// int[] currentTuple = new int[tuples[0].length];
			for (int i = 0; i < tuples.length; i++) {
				for (int j = 0; j < currentTuple.length; j++)
					currentTuple[j] = ctr.scp[j].dom.toIdx(tuples[i][j]);
				root.addTuple(currentTuple, positive, domainSizes);
				if (previousTuple == null)
					previousTuple = currentTuple.clone();
				else {
					reduce(root, previousTuple, currentTuple);
					int[] tmp = previousTuple;
					previousTuple = currentTuple;
					currentTuple = tmp;
				}
			}
			System.out.println("mapsize = " + map.size());
			// constraint.setIndexValueSimilarity(true);
		}
		this.positive = positive;

		// int cnt = root.display(new int[constraint.getNbInvolvedVariables()], 0, 0);
		// System.out.println("cnt=" + cnt);
		root.buildSonsClasses();
		// root.display();
		// displayAllTuples(allowed);

		List<int[][]> list = new LinkedList<>();
		root.collectCompressedTuples(list, new int[ctr.scp.length][], 0);
		System.out.println("cnt=" + list.size());
		compressedTuples = Kit.intArray3D(list);

		// new int[list.size()][][];
		// Iterator<int[][]> it = list.iterator();
		// int i = 0;
		// while (it.hasNext())
		// compressedTuples[i++] = it.next();

		// display(compressedTuples);

	}

	@SuppressWarnings("unused")
	private void display(int[][][] compressedTuples) {
		for (int i = 0; i < compressedTuples.length; i++) {
			for (int j = 0; j < compressedTuples[i].length; j++)
				System.out.print("{" + Kit.join(compressedTuples[i][j]) + "}" + (j < compressedTuples[i].length - 1 ? "x" : ""));
			System.out.println();
		}
	}

	public TableCompressed1(Constraint ctr) {
		super(ctr);
	}

	public TableCompressed1(Constraint ctr, TableCompressed1 t) {
		this(ctr);
		compressedTuples = Kit.cloneDeeply(t.compressedTuples);
		positive = t.positive;
	}

	@Override
	public boolean checkIdxs(int[] idxs) {
		throw new MissingImplementationException();
	}
}
