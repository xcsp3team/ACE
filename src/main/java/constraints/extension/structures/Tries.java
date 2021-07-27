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

import java.util.stream.IntStream;

import constraints.Constraint;

public class Tries extends ExtensionStructure {

	/**
	 * The roots of tries. There is a trie per variable as in [Gent et al. Data structures for GAC for extensional constraints. CP'07]
	 */
	private final Node[] trieRoots;

	/**
	 * When set to true, the array childs of each node is initialized, what allows to iterate all childs of a node without traversing the parent. <br>
	 * It remains to prove that it represents an optimization. One drawback is space consumption.
	 */
	private boolean directAccess;

	private final int[] tmp;

	/**
	 * Used to memorize in which trie we are currently working.
	 */
	private int currentTrieIndex;

	class Node {
		int idx;

		Node parent;

		Node firstChild;

		Node firstSibling;

		Node[] childs;

		Node(int idx, Node parent) {
			this.idx = idx;
			this.parent = parent;
		}

		Node(int idx, Node parent, Node firstSibling) {
			this(idx, parent);
			this.firstSibling = firstSibling;
		}
	}

	private void addTuple(Node node, int[] tuple, int position) {
		if (position == tuple.length)
			return;

		// in the ith trie, the ith variable has been put as first variable ; see [Gent et al. CP'07]
		int adjustedPosition = position == 0 ? currentTrieIndex : position <= currentTrieIndex ? position - 1 : position;
		int a = firstRegisteredCtr().indexesMatchValues ? tuple[adjustedPosition]
				: firstRegisteredCtr().scp[adjustedPosition].dom.toIdx(tuple[adjustedPosition]);

		Node previousChild = null, currentChild = node.firstChild;
		while (currentChild != null && currentChild.idx <= a) {
			previousChild = currentChild;
			currentChild = currentChild.firstSibling;
		}
		Node child = null;
		if (previousChild == null) {
			child = new Node(a, node, node.firstChild);
			node.firstChild = child;
		} else if (previousChild.idx == a) {
			child = previousChild;
		} else {
			child = new Node(a, node, previousChild.firstSibling);
			previousChild.firstSibling = child;
		}
		addTuple(child, tuple, position + 1);
	}

	private void buildChildsArrays(Node node, int position) {
		if (position == trieRoots.length)
			return;
		int adjustedPosition = position == 0 ? currentTrieIndex : position <= currentTrieIndex ? position - 1 : position;
		node.childs = new Node[firstRegisteredCtr().scp[adjustedPosition].dom.initSize()];
		for (Node child = node.firstChild; child != null; child = child.firstSibling) {
			node.childs[child.idx] = child;
			buildChildsArrays(child, position + 1);
		}
	}

	@Override
	public void storeTuples(int[][] tuples, boolean allowedTuples) {
		for (int i = 0; i < trieRoots.length; i++) {
			currentTrieIndex = i;
			for (int[] tuple : tuples)
				addTuple(trieRoots[i], tuple, 0);
		}
		assert controlNode(trieRoots[0].firstChild, 0);
		if (directAccess)
			for (int i = 0; i < trieRoots.length; i++) {
				currentTrieIndex = i;
				buildChildsArrays(trieRoots[i], 0);
			}
	}

	public Tries(Constraint ctr, boolean directAccess) {
		super(ctr);
		this.directAccess = directAccess;
		// roots of tries are built ; -1 as special index and null as parent
		this.trieRoots = IntStream.range(0, ctr.scp.length).mapToObj(i -> new Node(-1, null)).toArray(Node[]::new);
		this.tmp = new int[trieRoots.length];
	}

	@Override
	public boolean checkIdxs(int[] idxs) {
		return nextSupport(0, idxs[0], idxs) == idxs;
	}

	/**
	 * Put as attribute to avoid passing it at each recursive call of seeknextTuple
	 */
	private int[] current;

	private int[] seekNextTuple(Node node, int position) {
		if (position == current.length)
			return current;

		int realPosition = position <= currentTrieIndex ? position - 1 : position;
		int a = current[realPosition];

		Node child = null;
		if (directAccess) {
			child = node.childs[a];
			if (child != null) {
				int[] t = seekNextTuple(child, position + 1);
				if (t != null)
					return t;
				child = child.firstSibling;
			} else {
				child = node.firstChild;
				while (child != null && child.idx < a)
					child = child.firstSibling;
			}
		} else {
			child = node.firstChild;
			while (child != null && child.idx < a)
				child = child.firstSibling;
			if (child != null && child.idx == a) {
				int[] t = seekNextTuple(child, position + 1);
				if (t != null)
					return t;
				child = child.firstSibling;
			}
		}
		if (child == null)
			return null;
		for (int i = 1; i < position; i++) {
			realPosition = i <= currentTrieIndex ? i - 1 : i;
			tmp[realPosition] = current[realPosition];
		}
		for (int i = position; i < current.length; i++) {
			tmp[i <= currentTrieIndex ? i - 1 : i] = child.idx;
			child = child.firstChild;
		}
		return tmp;
	}

	@Override
	public int[] nextSupport(int x, int a, int[] current) {
		currentTrieIndex = x;
		this.current = current;
		tmp[x] = a;
		if (directAccess) {
			Node child = trieRoots[currentTrieIndex].childs[a];
			return child == null ? null : seekNextTuple(child, 1);
		}
		Node child = trieRoots[currentTrieIndex].firstChild;
		while (child != null && child.idx < a)
			child = child.firstSibling;
		return child == null || child.idx > a ? null : seekNextTuple(child, 1);
	}

	public int display(Node node, int position) {
		System.out.println(position + " " + node.idx);
		int cnt = position == trieRoots.length - 1 ? 1 : 0;
		for (Node child = node.firstChild; child != null; child = child.firstSibling)
			cnt += display(child, position + 1);
		return cnt;
	}

	public void display() {
		for (int i = 0; i < trieRoots.length; i++)
			System.out.println(" Position " + i + "\nNb tuples = " + display(trieRoots[i], -1));
	}

	private boolean controlNode(Node node, int position) {
		if (node == null)
			return true;
		if (!firstRegisteredCtr().scp[position].dom.contains(node.idx))
			return false;
		return controlNode(node.firstSibling, position) && controlNode(node.firstChild, position + 1);
	}
}
