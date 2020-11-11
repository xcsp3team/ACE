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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import org.xcsp.common.structures.Transitions;

import utility.Kit;

public final class MDDCD {

	public MDDNodeCD root;

	private Map<Integer, List<MDDNodeCD>> hashManager = new HashMap<>(2000);

	private Integer nNodes;

	public static MDDCD copy(MDDCD mdd) {
		MDDCD m = new MDDCD();
		m.root = MDDNodeCD.copy(mdd.root);
		return m;
	}

	public Integer nNodes() {
		return 2 + root.nInternalNodes(new HashSet<Integer>());
		// return nNodes != null ? nNodes : (nNodes = 2 + root.nInternalNodes(new HashSet<Integer>()));
	}

	private MDDNodeCD recursiveReduction(MDDNodeCD node) {
		if (node.isLeaf())
			return node;
		for (int i = 0; i < node.size; i++) {
			int v = node.dense[i];
			node.insert(v, recursiveReduction(node.sons[v]));
		}
		int hash = node.signature();
		List<MDDNodeCD> list = hashManager.computeIfAbsent(hash, h -> new ArrayList<>());
		for (MDDNodeCD n : list)
			if (node.similarTo(n))
				return n;
		list.add(node);
		return node;
	}

	public void recursiveRenaming() {
		int nNodes = root.renameNodes(1, new HashMap<Integer, MDDNodeCD>()) + 1;
		Kit.log.info("MDD : nNodes=" + nNodes + " nBuiltNodes=" + MDDNodeCD.nBuiltNodes);
	}

	public MDDCD(int[]... tuples) {
		// System.out.println("Storing tuples");
		this.root = new MDDNodeCD();
		for (int[] tuple : tuples)
			root.addTuple(tuple);
		recursiveReduction(this.root);
		recursiveRenaming();
	}

	public MDDCD(int uniqueValue) {
		this(new int[][] { { uniqueValue } });
	}

	public MDDCD(MDDCD mdd) {
		this.root = new MDDNodeCD(mdd.root, new HashMap<Integer, MDDNodeCD>());
		recursiveRenaming();
	}

	// or
	public MDDCD(MDDCD mdd1, MDDCD mdd2) {
		this.root = MDDNodeCD.or(0, mdd1.root, mdd2.root);
		// System.out.println("before reduction 1");
		// this.root.display(0, new HashMap<Integer, MDDNodeFake>());
		// System.out.println("nNodes1=" + nNodes());
		recursiveReduction(this.root);
		// System.out.println("nNodes2=" + nNodes());
		// System.out.println("before reduction 2");
		// this.root.display(0, new HashMap<Integer, MDDNodeFake>());
		recursiveRenaming();
	}

	public static MDDCD concat(MDDCD... sequence) {
		int offset = sequence[0].nNodes() - 2; // -2 because nodeF and nodeT
		for (int i = 1; i < sequence.length; i++) {
			sequence[i].root.renameNodeIds(offset, new HashMap<Integer, MDDNodeCD>());
			offset += sequence[i].nNodes() - 2; // -2 because nodeF and nodeT
		}
		for (int i = 0; i < sequence.length - 1; i++)
			sequence[i].root.replaceTrueNode(sequence[i + 1].root); // we replace the occurrence of nodeT in the ith mdd by the root of the i+1th mdd
		return sequence[0];
	}

	public Transitions transitions() {
		Transitions trs = new Transitions();
		root.transitions(trs, new HashMap<Integer, MDDNodeCD>());
		return trs;

	}

	public void displayTuples() {
		int cnt = root.displayTuples(0, new ArrayList<>());
		System.out.println("Cnt=" + cnt);
	}

	// public void displayTransitions() {
	// root.transitions(trs, map);displayTuples(0, new ArrayList<>());
	// System.out.println("Cnt=" + cnt);
	// }

	// public static void main(String[] args) {
	// int[][] tuples26 = { { 26 } };
	// int[][] tuples1 = { { 0 }, { 1 }, { 2 } };
	// int[][] tuples2 = { { 0, 0 }, { 1, 1 }, { 1, 2 }, { 2, 0 }, { 2, 2 } };
	// int[][] tuples3 = { { 0, 0, 1 }, { 0, 2, 1 }, { 1, 1, 0 }, { 1, 1, 2 }, { 2, 0, 1 }, { 2, 1, 1 } };
	// int[][] tuples4 = { { 0, 1, 1, 1 }, { 0, 1, 2, 1 }, { 1, 0, 1, 1 }, { 1, 0, 1, 2 }, { 1, 1, 0, 1 }, { 1, 1, 1, 0 } };
	//
	// // MDDFake f1 = new MDDFake(tuples1);
	// MDDSplit2 f3 = new MDDSplit2(tuples3);
	// MDDSplit2 f26 = new MDDSplit2(tuples26);
	// MDDSplit2 f4 = new MDDSplit2(tuples4);
	//
	// MDDSplit2 f = concat(new MDDSplit2(f3), new MDDSplit2(f26), new MDDSplit2(f4));
	// f.displayTuples();
	//
	// MDDSplit2 g = concat(new MDDSplit2(f4), new MDDSplit2(f26), new MDDSplit2(f3));
	// g.displayTuples();
	//
	// MDDSplit2 h = new MDDSplit2(f, g);
	// h.displayTuples();
	// h.root.display(0, new HashMap<Integer, MDDNodeSplit2>());
	//
	// int[][] tuplesor1 = { { 0, 0, 0, 0 }, { 0, 0, 1, 1 } };
	// int[][] tuplesor2 = { { 0, 1, 0, 0 }, { 0, 1, 1, 1 } };
	//
	// // MDDFake fo1 = new MDDFake(tuplesor1);
	// // MDDFake fo2 = new MDDFake(tuplesor2);
	// // MDDFake fm = new MDDFake(fo1, fo2);
	// // System.out.println("fm");
	// // fm.root.display(0, new HashMap<Integer, MDDNodeFake>());
	//
	// // merge(new MDDFake(f3), new MDDFake(f26), new MDDFake(f4));
	//
	// // f26.root.renameNodeIds(f3.nNodes() - 2, new HashMap<Integer, MDDNodeFake>());
	// // System.out.println("yo1");
	// // f26.root.display(0, new HashMap<Integer, MDDNodeFake>());
	// // f4.root.renameNodeIds(f3.nNodes() - 2 + f26.nNodes() - 2, new HashMap<Integer, MDDNodeFake>());
	// // System.out.println("yo2");
	// // f4.root.display(0, new HashMap<Integer, MDDNodeFake>());
	// //
	// // f3.root.replaceTrueNode(f26.root);
	// // System.out.println("yo3");
	// // f3.root.display(0, new HashMap<Integer, MDDNodeFake>());
	// //
	// // f26.root.replaceTrueNode(f4.root);
	// // System.out.println("yo4");
	// // f3.root.display(0, new HashMap<Integer, MDDNodeFake>());
	// }

}
