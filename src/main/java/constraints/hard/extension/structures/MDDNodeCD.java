/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension.structures;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.structures.Transitions;

import utility.Kit;

public final class MDDNodeCD {

	public static int nBuiltNodes;

	public final static MDDNodeCD nodeF = new MDDNodeCD(); // with id = 0

	public final static MDDNodeCD nodeT = new MDDNodeCD(); // with id = 1

	public final static int N_SONS = 27; // value 26 stands for BP (black point)

	public static MDDNodeCD copy(MDDNodeCD node) {
		return node == nodeT ? nodeT : new MDDNodeCD(node, new HashMap<Integer, MDDNodeCD>());
	}

	public static MDDNodeCD or(int level, MDDNodeCD node1, MDDNodeCD node2) {
		MDDNodeCD node = new MDDNodeCD();
		int i1 = 0, i2 = 0;
		while (i1 < node1.size && i2 < node2.size) {
			int v1 = node1.dense[i1], v2 = node2.dense[i2];
			if (v1 < v2) {
				node.insert(v1, copy(node1.sons[v1]));
				i1++;
			} else if (v1 > v2) {
				node.insert(v2, copy(node2.sons[v2]));
				i2++;
			} else {
				node.insert(v1, or(level + 1, node1.sons[v1], node2.sons[v2]));
				i1++;
				i2++;
			}
		}
		while (i1 < node1.size) {
			int v1 = node1.dense[i1];
			node.insert(v1, copy(node1.sons[v1]));
			i1++;
		}
		while (i2 < node2.size) {
			int v2 = node2.dense[i2];
			node.insert(v2, copy(node2.sons[v2]));
			i2++;
		}
		return node;
	}

	private static boolean discardClassForNodeF = true; // hard coding

	/**********************************************************************************************
	 * End of static section
	 *********************************************************************************************/

	/** The id of this node (must be unique) */
	public int id;

	/** All children (sons) of this node */
	public MDDNodeCD[] sons;

	public int[] dense;

	public int size;

	public int[][] sonsClasses;

	private Integer nSonsDifferentFromNodeF;

	public int nSonsDifferentFromNodeF() {
		return nSonsDifferentFromNodeF != null ? nSonsDifferentFromNodeF : (nSonsDifferentFromNodeF = (int) Stream.of(sons).filter(c -> c != nodeF).count());
	}

	public void insert(int v, MDDNodeCD node) {
		if (sons[v] == nodeF) {
			int i = 0;
			while (i < size && dense[i] < v)
				i++;
			assert i >= size || dense[i] != v : v + " " + i;
			for (int j = size; j > i; j--)
				dense[j] = dense[j - 1];
			dense[i] = v;
			size++;
		}
		sons[v] = node;
	}

	public String name() {
		return this == nodeF ? "nodeF" : this == nodeT ? "nodeT" : "n" + id;
	}

	public final boolean isLeaf() {
		return this == nodeF || this == nodeT;
	}

	public MDDNodeCD() {
		this.id = nBuiltNodes++;
		this.sons = new MDDNodeCD[N_SONS];
		Arrays.fill(this.sons, nodeF); // for (int i=0; i< IntStream.range(0, N_SONS).mapToObj(i -> nodeF).toArray(MDDNodeCD[]::new);
		this.dense = new int[N_SONS];
		this.size = 0;
	}

	public MDDNodeCD(MDDNodeCD node, Map<Integer, MDDNodeCD> map) {
		this();
		for (int i = 0; i < node.size; i++) {
			int v = node.dense[i];
			MDDNodeCD son = node.sons[v];
			assert son != nodeF;
			if (son == nodeT)
				insert(v, nodeT);
			else if (map.containsKey(son.id))
				this.insert(v, map.get(son.id));
			else {
				MDDNodeCD clone = new MDDNodeCD(son, map);
				map.put(son.id, clone);
				this.insert(v, clone);
			}
		}
	}

	public void buildSonsClasses() {
		if (isLeaf() || sonsClasses != null)
			return; // already built
		Map<MDDNodeCD, List<Integer>> map = IntStream.range(0, sons.length).filter(i -> !discardClassForNodeF || sons[i] != nodeF).boxed()
				.collect(Collectors.groupingBy(i -> sons[i]));
		sonsClasses = map.values().stream().map(list -> Kit.intArray(list)).toArray(int[][]::new);
		Stream.of(sons).forEach(s -> s.buildSonsClasses());
	}

	public boolean similarTo(MDDNodeCD other) {
		if (size != other.size)
			return false;
		for (int i = 0; i < size; i++)
			if (dense[i] != other.dense[i] || sons[dense[i]].id != other.sons[dense[i]].id)
				return false;
		return true;
	}

	public int signature() {
		int result = 1; // code from Arrays.hashcode()
		for (int i = 0; i < size; i++) {
			result = 31 * result + dense[i];
			result = 31 * result + sons[dense[i]].id;
		}
		return result;
	}

	private void addTuple(int level, int[] tuple) {
		int v = tuple[level];
		if (level == tuple.length - 1)
			insert(v, nodeT);
		else {
			if (sons[v] == nodeF)
				insert(v, new MDDNodeCD());
			sons[v].addTuple(level + 1, tuple);
		}
	}

	public void addTuple(int[] tuple) {
		addTuple(0, tuple);
	}

	public void renameNodeIds(int offset, Map<Integer, MDDNodeCD> map) {
		if (isLeaf() || map.get(id) == this)
			return;
		id += offset;
		map.put(id, this);
		for (int i = 0; i < size; i++)
			sons[dense[i]].renameNodeIds(offset, map);
	}

	public void replaceTrueNode(MDDNodeCD newNode) {
		if (isLeaf())
			return;
		for (int i = 0; i < size; i++) {
			int v = dense[i];
			if (sons[v] == nodeT)
				sons[v] = newNode;
			else if (sons[v] != newNode)
				sons[v].replaceTrueNode(newNode);
		}
	}

	public int renameNodes(int lastId, Map<Integer, MDDNodeCD> map) {
		if (isLeaf() || map.get(id) == this)
			return lastId;
		lastId++;
		map.put(id = lastId, this);
		for (int i = 0; i < size; i++)
			lastId = sons[dense[i]].renameNodes(lastId, map);
		// for (int i = 0; i < childClasses.length; i++) lastId = childs[childClasses[i][0]].renameNodes(lastId, map); // alternative
		return lastId;
	}

	public int nInternalNodes(Set<Integer> set) {
		if (isLeaf() || set.contains(id))
			return 0; // static leaves are not counted here and nodes with id already present in the set are already counted
		set.add(id);
		int sum = 1;
		for (int i = 0; i < size; i++)
			sum += sons[dense[i]].nInternalNodes(set);
		return sum;
	}

	// public boolean controlUniqueNodes(Map<Integer, MDDNodeSplit2> map) {
	// MDDNodeSplit2 node = map.get(id);
	// if (node == null)
	// map.put(id, this);
	// else
	// Kit.control(node == this, () -> "two nodes with the same id in the MDD " + id);
	// return sons == null || IntStream.range(0, N_SONS).filter(i -> sons[i] != nodeF).allMatch(i -> sons[i].controlUniqueNodes(map));
	// }

	public void transitions(Transitions trs, Map<Integer, MDDNodeCD> map) {
		if (isLeaf() || map.get(id) == this)
			return;
		map.put(id, this);
		for (int i = 0; i < size; i++) {
			int v = dense[i];
			trs.add(id == 2 ? "r" : "n" + id, v, "n" + sons[v].id);
			sons[v].transitions(trs, map);
		}
	}

	public int displayTuples(int cnt, List<Integer> list) {
		if (this.isLeaf()) {
			System.out.println(Kit.join(list));
			return cnt + 1;
		} else {
			for (int i = 0; i < size; i++) {
				int v = dense[i];
				list.add(v);
				cnt = sons[v].displayTuples(cnt, list);
				list.remove(list.size() - 1);
			}
			return cnt;
		}
	}

	public void display(int level, Map<Integer, MDDNodeCD> map) {
		if (this.isLeaf() || map.get(id) == this)
			return;
		map.put(id, this);
		System.out.println(
				id + "@" + level + " => {" + IntStream.range(0, size).mapToObj(i -> dense[i] + ":" + sons[dense[i]].id).collect(Collectors.joining(",")) + "}");
		IntStream.range(0, size).filter(i -> sons[dense[i]].id > id).forEach(i -> sons[dense[i]].display(level + 1, map));
	}

}
