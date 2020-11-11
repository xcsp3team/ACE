/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension.structures;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;

import utility.Kit;
import variables.domains.Domain;

public final class MDDNode {

	public final static MDDNode nodeF = new MDDNode(null, 0); // with id = 0

	public final static MDDNode nodeT = new MDDNode(null, 1); // with id = 1

	public static int nBuiltNodes;

	private static boolean discardClassForNodeF = true; // hard coding

	/**********************************************************************************************
	 * End of static section
	 *********************************************************************************************/

	/** The MDD to which belongs this node. */
	private final MDD mdd;

	/** The id of this node (must be unique) */
	public int id;

	/** The level of this node in the MDD to which it belongs */
	public final int level;

	/** All children (sons) of this node */
	public MDDNode[] sons;

	/**
	 * sonsClasses[i][j] is the index of the jth son in the ith equivalence class. Two indexes belong to the same class iff they reach the same child
	 */
	public int[][] sonsClasses;

	private Integer nSonsDifferentFromNodeF;

	/** Object used when building an MDD from an automaton or a KnapsSack; can be an Integer or a String */
	public Object state;

	public String name() {
		return this == nodeF ? "nodeF" : this == nodeT ? "nodeT" : level == 0 ? "root" : "n" + id;
	}

	public int nSonsDifferentFromNodeF() {
		return nSonsDifferentFromNodeF != null ? nSonsDifferentFromNodeF : (nSonsDifferentFromNodeF = (int) Stream.of(sons).filter(c -> c != nodeF).count());
	}

	public final boolean isLeaf() {
		return this == nodeF || this == nodeT;
	}

	private MDDNode(MDD mdd, int level) {
		this.mdd = mdd;
		if (mdd == null) {
			this.id = level;
			this.level = -1;
		} else {
			this.id = mdd.nextNodeId();
			this.level = level;
		}
	}

	public MDDNode(MDD mdd, int level, int nSons, boolean defaultNodeF) {
		this(mdd, level);
		this.sons = IntStream.range(0, nSons).mapToObj(i -> defaultNodeF ? nodeF : nodeT).toArray(MDDNode[]::new);
	}

	public MDDNode(MDD mdd, int level, int nSons, boolean defaultNodeF, Object state) {
		this(mdd, level, nSons, defaultNodeF);
		this.state = state;
	}

	private void addTuple(int level, int value, int[] tuple, boolean positive, int[] domSizes) {
		MDDNode son = sons[value];
		if (!son.isLeaf())
			son.addTuple(level + 1, tuple, positive, domSizes);
		else if (level == tuple.length - 1)
			sons[value] = positive ? nodeT : nodeF;
		else
			(sons[value] = new MDDNode(mdd, level + 1, domSizes[level + 1], positive)).addTuple(level + 1, tuple, positive, domSizes);
	}

	private void addTuple(int level, int[] tuple, boolean positive, int[] domSizes) {
		if (tuple[level] == Constants.STAR) {
			for (int i = 0; i < sons.length; i++)
				addTuple(level, i, tuple, positive, domSizes);
		} else
			addTuple(level, tuple[level], tuple, positive, domSizes);
	}

	public void addTuple(int[] tuple, boolean positive, int[] domSizes) {
		addTuple(0, tuple, positive, domSizes);
	}

	public void buildSonsClasses() {
		if (isLeaf() || sonsClasses != null)
			return; // already built
		Map<MDDNode, List<Integer>> map = IntStream.range(0, sons.length).filter(i -> !discardClassForNodeF || sons[i] != nodeF).boxed()
				.collect(Collectors.groupingBy(i -> sons[i]));
		sonsClasses = map.values().stream().map(list -> Kit.intArray(list)).toArray(int[][]::new);
		Stream.of(sons).forEach(s -> s.buildSonsClasses());
	}

	public int nInternalNodes(Set<Integer> set) {
		if (isLeaf() || set.contains(id))
			return 0; // static leaves are not counted here and nodes with id already in set are already counted
		set.add(id);
		return 1 + Stream.of(sons).mapToInt(c -> c.nInternalNodes(set)).sum();
	}

	private boolean canReachNodeT(Set<Integer> reachingNodes, Set<Integer> unreachingNodes) {
		if (this == nodeT || reachingNodes.contains(id))
			return true;
		if (this == nodeF || unreachingNodes.contains(id))
			return false;
		boolean found = false;
		for (int i = 0; i < sons.length; i++)
			if (!sons[i].canReachNodeT(reachingNodes, unreachingNodes))
				sons[i] = nodeF;
			else
				found = true;
		if (found)
			reachingNodes.add(id);
		else
			unreachingNodes.add(id);
		return found;
	}

	public boolean canReachNodeT() {
		return canReachNodeT(new HashSet<Integer>(), new HashSet<Integer>());
	}

	public int renameNodes(int lastId, Map<Integer, MDDNode> map) {
		if (isLeaf() || map.get(id) == this)
			return lastId;
		lastId++;
		map.put(id = lastId, this);
		for (MDDNode son : sons)
			lastId = son.renameNodes(lastId, map);
		// for (int i = 0; i < childClasses.length; i++) lastId = childs[childClasses[i][0]].renameNodes(lastId, map); // alternative
		return lastId;
	}

	public boolean controlUniqueNodes(Map<Integer, MDDNode> map) {
		MDDNode node = map.get(id);
		if (node == null)
			map.put(id, this);
		else
			Kit.control(node == this, () -> "two nodes with the same id in the MDD " + id);
		return sons == null || Stream.of(sons).noneMatch(child -> !child.controlUniqueNodes(map));
	}

	public void display(int[] cnts, boolean displayClasses) {
		if (this.isLeaf())
			return;
		Kit.log.fine(id + "@" + level + " => ");
		if (cnts != null)
			cnts[level]++;
		if (sons == null)
			return;
		Kit.log.fine("{" + Stream.of(sons).map(child -> child.id + "").collect(Collectors.joining(",")) + "}");
		if (displayClasses) {
			if (sonsClasses != null)
				for (int i = 0; i < sonsClasses.length; i++)
					Kit.log.fine("class " + i + " => {" + Kit.join(sonsClasses[i]) + "}");
			Kit.log.fine("nNotFFChilds=" + nSonsDifferentFromNodeF);
		}
		// if (similarChilds != null) for (int i = 0; i < similarChilds.length; i++)childs[similarChilds[i][0]].display(constraint, cnts);
		// else
		Stream.of(sons).filter(s -> s.id > id).forEach(s -> s.display(cnts, displayClasses));
	}

	public void display() {
		display(null, false);
	}

	public int displayTuples(Domain[] doms, int[] currTuple, int currLevel, int cnt) {
		if (this == nodeT) { // && Kit.isArrayContainingValuesAllDifferent(currentTuple)) {
			Kit.log.info(Kit.join(currTuple));
			cnt++;
		}
		if (isLeaf())
			return cnt;
		for (int i = 0; i < sons.length; i++) {
			currTuple[currLevel] = doms[currLevel].toVal(i);
			cnt = sons[i].displayTuples(doms, currTuple, currLevel + 1, cnt);
		}
		return cnt;
	}

	private StringBuilder getTransitions(Domain[] doms, StringBuilder sb, Set<MDDNode> processedNodes) {
		if (sons != null) {
			for (int i = 0; i < sons.length; i++)
				if (sons[i] != nodeF)
					sb.append("(").append(name()).append(",").append(doms[level].toVal(i)).append(",").append(sons[i].name()).append(")");
			processedNodes.add(this);
			for (MDDNode son : sons)
				if (!processedNodes.contains(son))
					son.getTransitions(doms, sb, processedNodes);
		}
		return sb;
	}

	public String getTransitions(Domain[] doms) {
		return getTransitions(doms, new StringBuilder(), new HashSet<MDDNode>()).toString();
	}

	public void collectCompressedTuples(List<int[][]> list, int[][] t, int level) {
		if (this == nodeT)
			list.add(Kit.cloneDeeply(t));
		if (isLeaf())
			return;
		for (int i = 0; i < sonsClasses.length; i++) {
			t[level] = sonsClasses[i];
			MDDNode representativeChild = sons[sonsClasses[i][0]];
			representativeChild.collectCompressedTuples(list, t, level + 1);
		}
	}

	public MDDNode filter(int[][] values, int prevVal) {
		if (isLeaf())
			return this;
		// int left = -1;
		// for (int i = childs.length - 1; i >= 0; i--)
		// if (values[i] > prevVal && childs[i] != nodeF) {
		// left = i; break; }
		// MDDNode node = null;
		// if (left == -1) node = this;
		// else {
		MDDNode node = new MDDNode(mdd, level, sons.length, true);
		for (int i = 0; i < sons.length; i++)
			if (values[level][i] <= prevVal)
				node.sons[i] = sons[i];
		// }
		for (int i = 0; i < sons.length; i++)
			node.sons[i] = node.sons[i].filter(values, values[level][i]);
		return node;
	}
}
