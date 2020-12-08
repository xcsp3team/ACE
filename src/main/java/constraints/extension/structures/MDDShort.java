/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension.structures;

import static org.xcsp.common.Constants.STAR;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;

import constraints.Constraint;
import constraints.extension.ExtensionMDDShort;
import utility.Kit;
import utility.Kit.IntArrayHashKey;
import variables.Domain;
import variables.Variable;

public final class MDDShort extends ExtensionStructure {

	/**********************************************************************************************
	 * MDDNodeShort
	 *********************************************************************************************/

	public static final class MDDNodeShort {

		public final static MDDNodeShort nodeF = new MDDNodeShort(null, 0); // with id = 0

		public final static MDDNodeShort nodeT = new MDDNodeShort(null, 1); // with id = 1

		public static int nBuiltNodes;

		private static boolean discardClassForNodeF = true; // hard coding

		/** The MDD to which belongs this node. */
		private final MDDShort mdd;

		/** The id of this node (must be unique) */
		public int id;

		/** The level of this node in the MDD to which it belongs */
		public final int level;

		/** All children (sons) of this node */
		public MDDNodeShort[] sons;

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
			return nSonsDifferentFromNodeF != null ? nSonsDifferentFromNodeF
					: (nSonsDifferentFromNodeF = (int) Stream.of(sons).filter(c -> c != nodeF).count());
		}

		public final boolean isLeaf() {
			return this == nodeF || this == nodeT;
		}

		private MDDNodeShort(MDDShort mdd, int level) {
			this.mdd = mdd;
			if (mdd == null) {
				this.id = level;
				this.level = -1;
			} else {
				this.id = mdd.nextNodeId();
				this.level = level;
			}
		}

		public MDDNodeShort(MDDShort mdd, int level, int nSons, boolean defaultNodeF) {
			this(mdd, level);
			this.sons = IntStream.range(0, nSons + 1).mapToObj(i -> defaultNodeF ? nodeF : nodeT).toArray(MDDNodeShort[]::new); // +1 for STAR
		}

		public MDDNodeShort(MDDShort mdd, int level, int nSons, boolean defaultNodeF, Object state) {
			this(mdd, level, nSons, defaultNodeF);
			this.state = state;
		}

		private void addTuple(int level, int value, int[] tuple, boolean positive, int[] domSizes) {
			MDDNodeShort son = sons[value];
			if (!son.isLeaf())
				son.addTuple(level + 1, tuple, positive, domSizes);
			else if (level == tuple.length - 1)
				sons[value] = positive ? nodeT : nodeF;
			else
				(sons[value] = new MDDNodeShort(mdd, level + 1, domSizes[level + 1], positive)).addTuple(level + 1, tuple, positive, domSizes);
		}

		private void addTuple(int level, int[] tuple, boolean positive, int[] domSizes) {
			addTuple(level, tuple[level] == Constants.STAR ? sons.length - 1 : tuple[level], tuple, positive, domSizes); // for STAR, the special value is
																															// sons.length-1
		}

		public void addTuple(int[] tuple, boolean positive, int[] domSizes) {
			addTuple(0, tuple, positive, domSizes);
		}

		public void buildSonsClasses() {
			if (isLeaf() || sonsClasses != null)
				return; // already built
			Map<MDDNodeShort, List<Integer>> map = IntStream.range(0, sons.length).filter(i -> !discardClassForNodeF || sons[i] != nodeF).boxed()
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

		public int renameNodes(int lastId, Map<Integer, MDDNodeShort> map) {
			if (isLeaf() || map.get(id) == this)
				return lastId;
			lastId++;
			map.put(id = lastId, this);
			for (MDDNodeShort son : sons)
				lastId = son.renameNodes(lastId, map);
			// for (int i = 0; i < childClasses.length; i++) lastId = childs[childClasses[i][0]].renameNodes(lastId, map); // alternative
			return lastId;
		}

		public boolean controlUniqueNodes(Map<Integer, MDDNodeShort> map) {
			MDDNodeShort node = map.get(id);
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
				currTuple[currLevel] = i == sons.length - 1 ? Constants.STAR : doms[currLevel].toVal(i);
				cnt = sons[i].displayTuples(doms, currTuple, currLevel + 1, cnt);
			}
			return cnt;
		}

		private StringBuilder getTransitions(Domain[] doms, StringBuilder sb, Set<MDDNodeShort> processedNodes) {
			if (sons != null) {
				for (int i = 0; i < sons.length; i++)
					if (sons[i] != nodeF)
						sb.append("(").append(name()).append(",").append(i == sons.length - 1 ? "*" : doms[level].toVal(i)).append(",").append(sons[i].name())
								.append(")");
				processedNodes.add(this);
				for (MDDNodeShort son : sons)
					if (!processedNodes.contains(son))
						son.getTransitions(doms, sb, processedNodes);
			}
			return sb;
		}

		public String getTransitions(Domain[] doms) {
			return getTransitions(doms, new StringBuilder(), new HashSet<MDDNodeShort>()).toString();
		}

		public void collectCompressedTuples(List<int[][]> list, int[][] t, int level) {
			if (this == nodeT)
				list.add(Kit.cloneDeeply(t));
			if (isLeaf())
				return;
			for (int i = 0; i < sonsClasses.length; i++) {
				t[level] = sonsClasses[i];
				MDDNodeShort representativeChild = sons[sonsClasses[i][0]];
				representativeChild.collectCompressedTuples(list, t, level + 1);
			}
		}
	}

	/**********************************************************************************************
	 * MDDShort
	 *********************************************************************************************/

	public MDDNodeShort root;

	private Integer nNodes;

	private boolean reductionWhileProcessingTuples = false; // hard coding

	private int nCreatedNodes = 2; // because two two first pre-built nodes nodeF and nodeT

	public Integer nNodes() {
		return nNodes != null ? nNodes : (nNodes = 2 + root.nInternalNodes(new HashSet<Integer>()));
	}

	public int nextNodeId() {
		return nCreatedNodes++;
	}

	public MDDShort(ExtensionMDDShort c) {
		super(c);
	}

	public MDDShort(ExtensionMDDShort c, MDDNodeShort root) {
		this(c);
		this.root = root;
	}

	private MDDNodeShort recursiveReduction(MDDNodeShort node, Map<IntArrayHashKey, MDDNodeShort> reductionMap) {
		if (node.isLeaf())
			return node;
		for (int i = 0; i < node.sons.length; i++)
			node.sons[i] = recursiveReduction(node.sons[i], reductionMap);
		IntArrayHashKey hk = new IntArrayHashKey(Stream.of(node.sons).mapToInt(c -> c.id).toArray());
		return reductionMap.computeIfAbsent(hk, k -> node);
	}

	private void reduce(int[] prevTuple, int[] currTuple, Map<IntArrayHashKey, MDDNodeShort> reductionMap) {
		int i = 0;
		MDDNodeShort node = root;
		while (prevTuple[i] == currTuple[i]) {
			int v = prevTuple[i] == Constants.STAR ? node.sons.length - 1 : prevTuple[i];
			node = node.sons[v];
			i++;
		}
		// assuming that tuples come in lex ordering, we can definitively reduce the left branch
		int v = prevTuple[i] == Constants.STAR ? node.sons.length - 1 : prevTuple[i];
		node.sons[v] = recursiveReduction(node.sons[v], reductionMap);
	}

	private void finalizeStoreTuples() {
		root.buildSonsClasses();
		nNodes = root.renameNodes(1, new HashMap<Integer, MDDNodeShort>()) + 1;
		Kit.log.info("MDDShort : nNodes=" + nNodes + " nBuiltNodes=" + nCreatedNodes);
		assert root.controlUniqueNodes(new HashMap<Integer, MDDNodeShort>());
		// buildSplitter();
		// root.display();
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		// System.out.println("Storing tuples");
		Kit.control(positive && tuples.length > 0);
		Constraint ctr = firstRegisteredCtr();
		int[] domainSizes = Variable.domSizeArrayOf(ctr.scp, true);
		Map<IntArrayHashKey, MDDNodeShort> reductionMap = new HashMap<>(2000);
		this.root = new MDDNodeShort(this, 0, domainSizes[0], positive);
		if (ctr.indexesMatchValues) {
			for (int i = 0; i < tuples.length; i++) {
				root.addTuple(tuples[i], positive, domainSizes);
				if (reductionWhileProcessingTuples && i > 0)
					reduce(tuples[i - 1], tuples[i], reductionMap);
			}
		} else {
			int[] previousTuple = null, currentTuple = new int[tuples[0].length];
			for (int[] tuple : tuples) {
				for (int i = 0; i < currentTuple.length; i++)
					currentTuple[i] = tuple[i] == STAR ? STAR : ctr.scp[i].dom.toIdx(tuple[i]);
				root.addTuple(currentTuple, positive, domainSizes);
				if (reductionWhileProcessingTuples) {
					if (previousTuple == null)
						previousTuple = currentTuple.clone();
					else {
						reduce(previousTuple, currentTuple, reductionMap);
						int[] tmp = previousTuple;
						previousTuple = currentTuple;
						currentTuple = tmp;
					}
				}
			}
			// constraint.setIndexValueSimilarity(true);
		}
		if (!reductionWhileProcessingTuples)
			recursiveReduction(root, reductionMap);
		finalizeStoreTuples();
	}

	private boolean checkIdxs(int[] t, int level, MDDNodeShort node) {
		if (node == MDDNodeShort.nodeT)
			return true;
		if (node == MDDNodeShort.nodeF)
			return false;
		return checkIdxs(t, level + 1, node.sons[t[level]]) || checkIdxs(t, level + 1, node.sons[node.sons.length - 1]);
	}

	@Override
	public boolean checkIdxs(int[] t) {
		return checkIdxs(t, 0, root);
	}

	public void displayTuples() {
		int cnt = root.displayTuples(Variable.buildDomainsArrayFor(firstRegisteredCtr().scp), new int[firstRegisteredCtr().scp.length], 0, 0);
		Kit.log.info(" => " + cnt + " tuples");
	}

}
