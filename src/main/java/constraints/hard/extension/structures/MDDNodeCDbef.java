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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.xcsp.common.structures.Transitions;

import utility.Kit;

public final class MDDNodeCDbef {

	public static int nBuiltNodes;

	public final static MDDNodeCDbef nodeF = new MDDNodeCDbef(); // with id = 0

	public final static MDDNodeCDbef nodeT = new MDDNodeCDbef(); // with id = 1

	/**********************************************************************************************
	 * End of static section
	 *********************************************************************************************/

	/** The id of this node (must be unique) */
	public int id;

	/** All children (sons) of this node */
	public Map<Integer, MDDNodeCDbef> sons = new HashMap<>();

	// private int[] sortedKeys;

	public int[] sortedKeys() {
		return sons.keySet().stream().mapToInt(i -> i).sorted().toArray();
		// return sortedKeys != null ? sortedKeys : (sortedKeys = sons.keySet().stream().mapToInt(i -> i).sorted().toArray());
	}

	public String name() {
		return this == nodeF ? "nodeF" : this == nodeT ? "nodeT" : "n" + id;
	}

	public final boolean isLeaf() {
		return this == nodeF || this == nodeT;
	}

	public MDDNodeCDbef(MDDNodeCDbef node, Map<Integer, MDDNodeCDbef> map) {
		this.id = nBuiltNodes++; // node.id;
		for (int key : node.sons.keySet()) {
			MDDNodeCDbef f = node.sons.get(key);
			if (f == nodeT)
				this.sons.put(key, nodeT);
			else if (map.containsKey(f.id))
				this.sons.put(key, map.get(f.id));
			else {
				MDDNodeCDbef m = new MDDNodeCDbef(f, map);
				map.put(f.id, m);
				this.sons.put(key, m);
			}
		}
	}

	public MDDNodeCDbef() {
		this.id = nBuiltNodes++;
	}

	public static MDDNodeCDbef or(int level, MDDNodeCDbef f1, MDDNodeCDbef f2) {
		MDDNodeCDbef r = new MDDNodeCDbef();
		int[] keys1 = f1.sortedKeys(), keys2 = f2.sortedKeys();
		int i1 = 0, i2 = 0;
		while (i1 < keys1.length && i2 < keys2.length) {
			// System.out.println(level + " :" + i1 + " " + i2 + " keys " + keys1[i1] + " " + keys2[i2]);
			if (keys1[i1] < keys2[i2]) {
				r.sons.put(keys1[i1], f1.sons.get(keys1[i1]) == nodeT ? nodeT : new MDDNodeCDbef(f1.sons.get(keys1[i1]), new HashMap<Integer, MDDNodeCDbef>()));
				i1++;
			} else if (keys1[i1] > keys2[i2]) {
				r.sons.put(keys2[i2], f2.sons.get(keys2[i2]) == nodeT ? nodeT : new MDDNodeCDbef(f2.sons.get(keys2[i2]), new HashMap<Integer, MDDNodeCDbef>()));
				i2++;
			} else {
				r.sons.put(keys1[i1], or(level + 1, f1.sons.get(keys1[i1]), f2.sons.get(keys2[i2])));
				i1++;
				i2++;
			}
		}
		while (i1 < keys1.length) {
			r.sons.put(keys1[i1], f1.sons.get(keys1[i1]) == nodeT ? nodeT : new MDDNodeCDbef(f1.sons.get(keys1[i1]), new HashMap<Integer, MDDNodeCDbef>()));
			i1++;
		}
		while (i2 < keys2.length) {
			r.sons.put(keys2[i2], f2.sons.get(keys2[i2]) == nodeT ? nodeT : new MDDNodeCDbef(f2.sons.get(keys2[i2]), new HashMap<Integer, MDDNodeCDbef>()));
			i2++;
		}
		return r;

	}

	public int[] signature() {
		int[] t = new int[sortedKeys().length * 2];
		int nb = 0;
		for (int key : sortedKeys()) {
			t[nb++] = key;
			t[nb++] = sons.get(key).id;
		}
		return t;
	}

	private void addTuple(int level, int[] tuple) {
		if (level == tuple.length - 1)
			sons.put(tuple[level], nodeT);
		else
			sons.computeIfAbsent(tuple[level], v -> new MDDNodeCDbef()).addTuple(level + 1, tuple);
	}

	public void addTuple(int[] tuple) {
		addTuple(0, tuple);
	}

	public void renameNodeIds(int offset, Map<Integer, MDDNodeCDbef> map) {
		if (isLeaf() || map.get(id) == this)
			return;
		id += offset;
		map.put(id, this);
		for (MDDNodeCDbef son : sons.values())
			son.renameNodeIds(offset, map);
	}

	public void replaceTrueNode(MDDNodeCDbef newNode) {
		if (isLeaf())
			return;
		for (int key : sons.keySet()) {
			if (sons.get(key) == nodeT) {
				sons.put(key, newNode);
			} else {
				// System.out.println("node" + sons.get(key).id);
				if (sons.get(key) != newNode)
					sons.get(key).replaceTrueNode(newNode);
			}
		}
	}

	public int renameNodes(int lastId, Map<Integer, MDDNodeCDbef> map) {
		if (isLeaf() || map.get(id) == this)
			return lastId;
		lastId++;
		map.put(id = lastId, this);
		for (MDDNodeCDbef son : sons.values())
			lastId = son.renameNodes(lastId, map);
		// for (int i = 0; i < childClasses.length; i++) lastId = childs[childClasses[i][0]].renameNodes(lastId, map); // alternative
		return lastId;
	}

	public int nInternalNodes(Set<Integer> set) {
		if (isLeaf() || set.contains(id))
			return 0; // static leaves are not counted here and nodes with id already present in the set are already counted
		set.add(id);
		return 1 + sons.values().stream().mapToInt(c -> c.nInternalNodes(set)).sum();
	}

	public boolean controlUniqueNodes(Map<Integer, MDDNodeCDbef> map) {
		MDDNodeCDbef node = map.get(id);
		if (node == null)
			map.put(id, this);
		else
			Kit.control(node == this, () -> "two nodes with the same id in the MDD " + id);
		return sons == null || sons.values().stream().allMatch(n -> n.controlUniqueNodes(map));
	}

	public void transitions(Transitions trs, Map<Integer, MDDNodeCDbef> map) {
		if (isLeaf() || map.get(id) == this)
			return;
		map.put(id, this);
		for (int key : sortedKeys()) {
			trs.add(id == 2 ? "r" : "n" + id, key, "n" + sons.get(key).id);
			sons.get(key).transitions(trs, map);
		}

	}

	// public boolean controlLeaves(int level, int maxLevel, Map<Integer, MDDNodeFake> map) {
	// if (level == maxLevel && this != nodeT)
	// return false;
	// if (map.get(id) == this)
	// return true;
	// map.put(id, this);
	// for (int key : sortedKeys())
	// if (!sons.get(key).controlLeaves(level + 1, maxLevel, map))
	// return false;
	// return true;
	// }

	public int displayTuples(int cnt, List<Integer> list) {
		if (this.isLeaf()) {
			System.out.println(Kit.join(list));
			return cnt + 1;
		} else {
			for (int key : this.sortedKeys()) {
				list.add(key);
				cnt = sons.get(key).displayTuples(cnt, list);
				list.remove(list.size() - 1);
			}
			return cnt;
		}
	}

	public void display(int level, Map<Integer, MDDNodeCDbef> map) {
		if (this.isLeaf() || map.get(id) == this)
			return;
		map.put(id, this);
		System.out.println(
				id + "@" + level + " => {" + IntStream.of(sortedKeys()).mapToObj(key -> key + ":" + sons.get(key).id).collect(Collectors.joining(",")) + "}");
		sons.values().stream().filter(n -> n.id > id).forEach(n -> n.display(level + 1, map));
	}

}
