/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension.structures;

import java.util.stream.IntStream;

import constraints.ConstraintExtension;

public class Tries extends ExtensionStructure {

	/**********************************************************************************************
	 * Intern class Node
	 *********************************************************************************************/

	private final class Node {
		int idx;

		Node parent;

		Node firstChild;

		Node firstSibling;

		Node[] sons;

		Node(int idx, Node parent) {
			this.idx = idx;
			this.parent = parent;
		}

		Node(int idx, Node parent, Node firstSibling) {
			this(idx, parent);
			this.firstSibling = firstSibling;
		}
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	@Override
	public boolean checkIndexes(int[] idxs) {
		return nextSupport(0, idxs[0], idxs) == idxs;
	}

	/**
	 * The roots of tries. There is a trie per variable as described in in "Data structures for GAC for extensional
	 * constraints", CP'07 by Gent et al.
	 */
	private final Node[] roots;

	/**
	 * When set to true, the array sons of each node is initialized, what allows us to iterate all sons of a node
	 * without traversing the parent. <br>
	 * It remains to prove that it represents an optimization. One drawback is space consumption.
	 */
	private boolean directAccess;

	private final int[] tmp;

	/**
	 * Used to memorize in which trie we are currently working.
	 */
	private int currentTrieIndex;

	public Tries(ConstraintExtension c, boolean directAccess) {
		super(c);
		this.directAccess = directAccess;
		// roots of tries are built ; -1 as special index and null as parent
		this.roots = IntStream.range(0, c.scp.length).mapToObj(i -> new Node(-1, null)).toArray(Node[]::new);
		this.tmp = new int[roots.length];
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
		if (position == roots.length)
			return;
		int adjustedPosition = position == 0 ? currentTrieIndex : position <= currentTrieIndex ? position - 1 : position;
		node.sons = new Node[firstRegisteredCtr().scp[adjustedPosition].dom.initSize()];
		for (Node child = node.firstChild; child != null; child = child.firstSibling) {
			node.sons[child.idx] = child;
			buildChildsArrays(child, position + 1);
		}
	}

	@Override
	public void storeTuples(int[][] tuples, boolean allowedTuples) {
		for (int i = 0; i < roots.length; i++) {
			currentTrieIndex = i;
			for (int[] tuple : tuples)
				addTuple(roots[i], tuple, 0);
		}
		assert controlNode(roots[0].firstChild, 0);
		if (directAccess)
			for (int i = 0; i < roots.length; i++) {
				currentTrieIndex = i;
				buildChildsArrays(roots[i], 0);
			}
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
			child = node.sons[a];
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
			Node child = roots[currentTrieIndex].sons[a];
			return child == null ? null : seekNextTuple(child, 1);
		}
		Node child = roots[currentTrieIndex].firstChild;
		while (child != null && child.idx < a)
			child = child.firstSibling;
		return child == null || child.idx > a ? null : seekNextTuple(child, 1);
	}

	public int display(Node node, int position) {
		System.out.println(position + " " + node.idx);
		int cnt = position == roots.length - 1 ? 1 : 0;
		for (Node child = node.firstChild; child != null; child = child.firstSibling)
			cnt += display(child, position + 1);
		return cnt;
	}

	public void display() {
		for (int i = 0; i < roots.length; i++)
			System.out.println(" Position " + i + "\nNb tuples = " + display(roots[i], -1));
	}

	private boolean controlNode(Node node, int position) {
		if (node == null)
			return true;
		if (!firstRegisteredCtr().scp[position].dom.contains(node.idx))
			return false;
		return controlNode(node.firstSibling, position) && controlNode(node.firstChild, position + 1);
	}
}
