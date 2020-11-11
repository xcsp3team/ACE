/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension.structures;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import org.xcsp.common.structures.Transitions;

import utility.Kit;

public final class MDDCDbef {

	public MDDNodeCDbef root;

	private Map<Integer, List<MDDNodeCDbef>> hashManager = new HashMap<>(2000);

	public Integer nNodes() {
		return 2 + root.nInternalNodes(new HashSet<Integer>());
		// return nNodes != null ? nNodes : (nNodes = 2 + root.nInternalNodes(new HashSet<Integer>()));
	}

	private MDDNodeCDbef recursiveReduction(MDDNodeCDbef node) {
		if (node.isLeaf())
			return node;
		for (int key : node.sons.keySet()) // node.sortedKeys()) // sons.keySet())
			node.sons.put(key, recursiveReduction(node.sons.get(key)));
		int[] t = node.signature();
		int hash = Arrays.hashCode(t);
		List<MDDNodeCDbef> list = hashManager.get(hash);
		if (list == null) {
			list = new ArrayList<>();
			list.add(node);
			hashManager.put(hash, list);
			return node;
		}
		for (MDDNodeCDbef n : list)
			if (Arrays.equals(t, n.signature()))
				return n;
		list.add(node);
		return node;
	}

	private void recursiveRenaming() {
		int nNodes = root.renameNodes(1, new HashMap<Integer, MDDNodeCDbef>()) + 1;
		Kit.log.info("MDD : nNodes=" + nNodes + " nBuiltNodes=" + MDDNodeCDbef.nBuiltNodes);
	}

	public MDDCDbef(int[]... tuples) {
		// System.out.println("Storing tuples");
		this.root = new MDDNodeCDbef();
		for (int i = 0; i < tuples.length; i++)
			root.addTuple(tuples[i]);
		recursiveReduction(this.root);
		recursiveRenaming();
	}

	public MDDCDbef(int uniqueValue) {
		this(new int[][] { { uniqueValue } });
	}

	public MDDCDbef(MDDCDbef f) {
		this.root = new MDDNodeCDbef(f.root, new HashMap<Integer, MDDNodeCDbef>());
		recursiveRenaming();

		// this.root.renameNodes(1, new HashMap<Integer, MDDNodeFake>());
	}

	// or
	public MDDCDbef(MDDCDbef f1, MDDCDbef f2) {
		this.root = MDDNodeCDbef.or(0, f1.root, f2.root);
		// System.out.println("before reduction 1");
		// this.root.display(0, new HashMap<Integer, MDDNodeFake>());
		System.out.println("nNodes1=" + nNodes());
		recursiveReduction(this.root);
		System.out.println("nNodes2=" + nNodes());
		// System.out.println("before reduction 2");
		// this.root.display(0, new HashMap<Integer, MDDNodeFake>());
		recursiveRenaming();
	}

	public static MDDCDbef concat(MDDCDbef... sequence) {
		int offset = sequence[0].nNodes() - 2; // -2 because nodeF and nodeT
		for (int i = 1; i < sequence.length; i++) {
			sequence[i].root.renameNodeIds(offset, new HashMap<Integer, MDDNodeCDbef>());
			offset += sequence[i].nNodes() - 2; // -2 because nodeF and nodeT
		}
		for (int i = 0; i < sequence.length - 1; i++)
			sequence[i].root.replaceTrueNode(sequence[i + 1].root); // we replace the occurrence of nodeT in the ith mdd by the root of the i+1th
		return sequence[0];
	}

	public Transitions transitions() {
		Transitions trs = new Transitions();
		root.transitions(trs, new HashMap<Integer, MDDNodeCDbef>());
		return trs;

	}

	// public boolean controlLeaves() {
	// return this.root.controlLeaves(0, 6, new HashMap<Integer, MDDNodeFake>());
	// }

	public void displayTuples() {
		int cnt = root.displayTuples(0, new ArrayList<>());
		System.out.println("Cnt=" + cnt);
	}

	public static void main(String[] args) {
		int[][] tuples26 = { { 26 } };
		int[][] tuples1 = { { 0 }, { 1 }, { 2 } };
		int[][] tuples2 = { { 0, 0 }, { 1, 1 }, { 1, 2 }, { 2, 0 }, { 2, 2 } };
		int[][] tuples3 = { { 0, 0, 1 }, { 0, 2, 1 }, { 1, 1, 0 }, { 1, 1, 2 }, { 2, 0, 1 }, { 2, 1, 1 } };
		int[][] tuples4 = { { 0, 1, 1, 1 }, { 0, 1, 2, 1 }, { 1, 0, 1, 1 }, { 1, 0, 1, 2 }, { 1, 1, 0, 1 }, { 1, 1, 1, 0 } };

		// MDDFake f1 = new MDDFake(tuples1);
		MDDCDbef f3 = new MDDCDbef(tuples3);
		MDDCDbef f26 = new MDDCDbef(tuples26);
		MDDCDbef f4 = new MDDCDbef(tuples4);

		MDDCDbef f = concat(new MDDCDbef(f3), new MDDCDbef(f26), new MDDCDbef(f4));
		f.displayTuples();

		MDDCDbef g = concat(new MDDCDbef(f4), new MDDCDbef(f26), new MDDCDbef(f3));
		g.displayTuples();

		MDDCDbef h = new MDDCDbef(f, g);
		h.displayTuples();
		h.root.display(0, new HashMap<Integer, MDDNodeCDbef>());

		int[][] tuplesor1 = { { 0, 0, 0, 0 }, { 0, 0, 1, 1 } };
		int[][] tuplesor2 = { { 0, 1, 0, 0 }, { 0, 1, 1, 1 } };

		// MDDFake fo1 = new MDDFake(tuplesor1);
		// MDDFake fo2 = new MDDFake(tuplesor2);
		// MDDFake fm = new MDDFake(fo1, fo2);
		// System.out.println("fm");
		// fm.root.display(0, new HashMap<Integer, MDDNodeFake>());

		// merge(new MDDFake(f3), new MDDFake(f26), new MDDFake(f4));

		// f26.root.renameNodeIds(f3.nNodes() - 2, new HashMap<Integer, MDDNodeFake>());
		// System.out.println("yo1");
		// f26.root.display(0, new HashMap<Integer, MDDNodeFake>());
		// f4.root.renameNodeIds(f3.nNodes() - 2 + f26.nNodes() - 2, new HashMap<Integer, MDDNodeFake>());
		// System.out.println("yo2");
		// f4.root.display(0, new HashMap<Integer, MDDNodeFake>());
		//
		// f3.root.replaceTrueNode(f26.root);
		// System.out.println("yo3");
		// f3.root.display(0, new HashMap<Integer, MDDNodeFake>());
		//
		// f26.root.replaceTrueNode(f4.root);
		// System.out.println("yo4");
		// f3.root.display(0, new HashMap<Integer, MDDNodeFake>());
	}

}
