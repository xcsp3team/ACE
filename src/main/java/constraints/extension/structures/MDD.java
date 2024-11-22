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

import static constraints.extension.structures.MDD.Node.nodeF;
import static constraints.extension.structures.MDD.Node.nodeT;
import static org.xcsp.common.Constants.STAR;
import static utility.Kit.control;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Condition;
import org.xcsp.common.Constants;
import org.xcsp.common.Range;
import org.xcsp.common.Utilities;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Transition;

import constraints.Constraint;
import constraints.extension.CMDD;
import constraints.extension.CMDD.CMDDO;
import constraints.extension.CMDD.CMDDS;
import utility.Kit;
import utility.Kit.IntArrayHashKey;
import variables.Domain;
import variables.Variable;

/**
 * This is the class for extension structures represented by Multi-valued Decision Diagrams (MDDs). All supports (allowed tuples) are recorded as paths in the
 * MDD. Note that tuples are recorded with indexes (of values).
 * 
 * @author Christophe Lecoutre
 */
public final class MDD extends ExtensionStructure {

	/**********************************************************************************************
	 * Intern class Node
	 *********************************************************************************************/

	/**
	 * The class for representing a node in an MDD
	 */
	public static final class Node {

		// Start STATIC part

		private static Map<String, List<Transition>> buildNextTransitions(Automaton automaton) {
			Map<String, List<Transition>> map = new HashMap<>();
			map.put(automaton.startState, new ArrayList<>());
			for (String s : automaton.finalStates)
				map.put(s, new ArrayList<>());
			for (Transition t : automaton.transitions) {
				if (!map.containsKey(t.start))
					map.put(t.start, new ArrayList<>());
				if (!map.containsKey(t.end))
					map.put(t.end, new ArrayList<>());
			}
			for (Transition t : automaton.transitions)
				map.get(t.start).add(t);
			return map;
		}

		public static Node buildRootFromAutomaton(Automaton automaton, Domain[] domains) {
			boolean starred = false; // false because for the moment necessarily called for a CMDDO
			control(domains.length > 1 && IntStream.range(1, domains.length).allMatch(i -> domains[i].typeIdentifier() == domains[0].typeIdentifier()));
			Node root = new Node(0, domains[0].initSize(), starred, true, automaton.startState);
			Map<String, List<Transition>> nextTrs = buildNextTransitions(automaton);
			Map<String, Node> prevs = new HashMap<>(), nexts = new HashMap<>();
			prevs.put((String) root.state, root);
			Object allValues = domains[0].allValues(); // remember that all domains have the same type
			int[] domValues = allValues instanceof Range ? ((Range) allValues).toArray() : (int[]) allValues;
			for (int i = 0; i < domains.length; i++) {
				for (Node node : prevs.values()) {
					for (Transition tr : nextTrs.get(node.state)) {
						int[] values = tr.value instanceof Condition ? ((Condition) tr.value).filtering(domValues)
								: new int[] { Utilities.safeInt((Long) tr.value) };
						for (int v : values) {
							int a = domains[i].toIdx(v);
							if (a != -1) {
								String nextState = tr.end;
								if (i == domains.length - 1) {
									node.sons[a] = Utilities.indexOf(nextState, automaton.finalStates) != -1 ? nodeT : nodeF;
								} else {
									// Node nextNode = nexts.computeIfAbsent(nextState, k -> new Node(this, i + 1, domains[i].initSize(), true, nextState)); //
									// pb
									// with i not final
									Node nextNode = nexts.get(nextState);
									if (nextNode == null)
										nexts.put(nextState, nextNode = new Node(i + 1, domains[i].initSize(), starred, true, nextState));
									node.sons[a] = nextNode;
								}
							}
						}
					}
				}
				Map<String, Node> tmp = prevs;
				prevs = nexts;
				nexts = tmp;
				nexts.clear();
			}
			root.finalizeRoot();
			return root;
		}

		public static Node buildRootFromTransitions(Transition[] transitions, Domain[] domains) {
			boolean starred = false; // false because for the moment necessarily called for a CMDDO
			Map<String, Node> nodes = new HashMap<>();
			Set<String> possibleRoots = new HashSet<>(), notRoots = new HashSet<>();
			Set<String> possibleWells = new HashSet<>(), notWells = new HashSet<>();
			for (Transition tr : transitions) {
				String src = tr.start, tgt = tr.end;
				notWells.add(src);
				notRoots.add(tgt);
				if (!notRoots.contains(src))
					possibleRoots.add(src);
				if (!notWells.contains(tgt))
					possibleWells.add(tgt);
				if (possibleRoots.contains(tgt))
					possibleRoots.remove(tgt);
				if (possibleWells.contains(src))
					possibleWells.remove(src);
			}
			control(possibleRoots.size() == 1 && possibleWells.size() == 1,
					() -> "sizes= " + possibleRoots.size() + " " + possibleWells.stream().collect(Collectors.joining(" ")));
			String sroot = possibleRoots.toArray(new String[1])[0];
			String swell = possibleWells.toArray(new String[1])[0];
			Node root = new Node(0, domains[0].initSize(), starred, true);
			nodes.put(sroot, root);
			nodes.put(swell, nodeT);
			// TODO reordering transitions to guarantee that the src node has already been generated
			for (Transition tr : transitions) {
				Node node1 = nodes.get(tr.start);
				long v = ((Number) tr.value).longValue(); // instanceof Integer ? (Integer) tr.value : (Long) tr.value;
				int val = Utilities.safeInt(v);
				int idx = domains[node1.level].toIdx(val);
				control(idx != -1);
				Node node2 = nodes.computeIfAbsent(tr.end, k -> new Node(node1.level + 1, domains[node1.level + 1].initSize(), starred, true));
				node1.sons[idx] = node2;
			}
			root.finalizeRoot(); // should we avoid root.canReachNodeT() during finalization?
			return root;
		}

		// coeffs, and limits (either a Range or an int array) from the knapsack constraint, and values are the possible values at each level
		public static Node buildRootFromKnapsack(int[] coeffs, Object limits, int[][] values) {
			boolean starred = false; // false because for the moment necessarily called for a CMDDO
			Node root = new Node(0, values[0].length, starred, true, 0);
			Map<Integer, Node> prevs = new HashMap<>(), nexts = new HashMap<>();
			prevs.put((Integer) root.state, root);
			for (int level = 0; level < coeffs.length; level++) {
				for (Node node : prevs.values()) {
					for (int j = 0; j < values[level].length; j++) {
						int nextState = (Integer) node.state + coeffs[level] * values[level][j];
						if (level == coeffs.length - 1) {
							if (limits instanceof Range)
								node.sons[j] = ((Range) limits).contains(nextState) ? nodeT : nodeF;
							else
								node.sons[j] = Utilities.indexOf(nextState, (int[]) limits) != -1 ? nodeT : nodeF;
						} else {
							Node nextNode = nexts.get(nextState);
							if (nextNode == null)
								nexts.put(nextState, nextNode = new Node(level + 1, values[level + 1].length, starred, true, nextState));
							node.sons[j] = nextNode;
						}
					}
				}
				Map<Integer, Node> tmp = prevs;
				prevs = nexts;
				nexts = tmp;
				nexts.clear();
			}

			boolean increasing = false;
			if (increasing) {
				root.canReachNodeT(); // necessary ?
				root = root.filter(values, Integer.MAX_VALUE);
				root.recursiveReduction(new HashMap<>(2000));
			}
			root.finalizeRoot();
			return root;
		}

		// TODO the code for reduce is broken; it does not currently work for starred tuples
		// the code must be updated for the case where starApart is false or true
		// private static void reduce(Node root, int[] prevTuple, int[] currTuple, Map<IntArrayHashKey, Node> reductionMap) {
		// int i = 0;
		// Node node = root;
		// while (prevTuple[i] == currTuple[i])
		// node = node.sons[prevTuple[i++]];
		// // assuming that tuples come in lex ordering, we can definitively reduce the left branch
		// node.sons[prevTuple[i]] = node.sons[prevTuple[i]].recursiveReduction(, reductionMap);
		// }

		private static void reduce(Node root, int[] prevTuple, int[] currTuple, Map<IntArrayHashKey, Node> reductionMap) {
			int i = 0;
			Node node = root;
			while (prevTuple[i] == currTuple[i]) {
				int v = prevTuple[i] == Constants.STAR ? node.sons.length - 1 : prevTuple[i];
				node = node.sons[v];
				i++;
			}
			// assuming that tuples come in lex ordering, we can definitively reduce the left branch
			int v = prevTuple[i] == Constants.STAR ? node.sons.length - 1 : prevTuple[i];
			node.sons[v] = node.sons[v].recursiveReduction(reductionMap);
		}

		public static Node buildRootFromTuples(int[][] tuples, boolean positive, Domain[] domains, boolean starred, boolean reductionWhileProcessingTuples) {
			// the last parameter indicates if one must try to reduce the MDD when processing tuples
			// TODO for the moment the code may be broken when true (is it still the case?) see reduce

			control(positive && tuples.length > 0);
			int[] domainSizes = Stream.of(domains).mapToInt(dom -> dom.initSize()).toArray();
			Map<IntArrayHashKey, Node> reductionMap = new HashMap<>(2000);
			Node root = new Node(0, domainSizes[0], starred, positive);
			if (Stream.of(domains).allMatch(dom -> dom.indexesMatchValues())) {
				// if (c.indexesMatchValues) {
				// System.out.println("nbtuples " + tuples.length);
				for (int i = 0; i < tuples.length; i++) {
					root.addTuple(tuples[i], positive, domainSizes);
					if (reductionWhileProcessingTuples && i > 0)
						reduce(root, tuples[i - 1], tuples[i], reductionMap);
					// if (i % 100 == 0)
					// System.out.println(" " + root.nInternalNodes(new HashSet<Integer>()));

				}
			} else {
				// we need to pass from tuples of values in tuples of indexes (of values)
				int[] previousTuple = null, currentTuple = new int[tuples[0].length];

				for (int[] tuple : tuples) {
					for (int i = 0; i < currentTuple.length; i++)
						currentTuple[i] = tuple[i] == STAR ? STAR : domains[i].toIdx(tuple[i]);
					root.addTuple(currentTuple, positive, domainSizes);
					if (reductionWhileProcessingTuples) {
						if (previousTuple == null)
							previousTuple = currentTuple.clone();
						else {
							reduce(root, previousTuple, currentTuple, reductionMap);
							int[] tmp = previousTuple;
							previousTuple = currentTuple;
							currentTuple = tmp;
						}
					}
				}
			}
			if (!reductionWhileProcessingTuples)
				root.recursiveReduction(reductionMap);
			root.finalizeRoot();
			return root;
		}

		// End STATIC part

		/**
		 * The number of nodes already created ; useful during construction of MDDs
		 */
		private static int nCreatedNodes;

		/**
		 * The False terminal node of the MDD (with id 0) ; node shared by all MDDs
		 */
		public static final Node nodeF = new Node(-1);

		/**
		 * The True terminal node of the MDD (with id 1) ; node shared by all MDDs
		 */
		public static final Node nodeT = new Node(-1);

		/**
		 * The num(ber) of this node (must be unique)
		 */
		public int num;

		/**
		 * The level of this node in the MDD to which it belongs
		 */
		public final int level;

		/**
		 * The children (sons) of this node
		 */
		public Node[] sons;

		/**
		 * Indicates if the last son is a special son for * (used for CMDDS)
		 */
		public boolean starred;

		/**
		 * Equivalence classes among sons of the node; sonsClasses[i][j] is the index of the jth son in the ith equivalence class. Two indexes belong to the
		 * same class iff they reach the same child.
		 */
		public int[][] classes;

		/**
		 * The number of sons that are different from the False terminal node. This is used as a cache (and useful when exploring with a MDD)
		 */
		private Integer nRelevantSons;

		/**
		 * Object used temporarily when building an MDD from an automaton or a KnapsSack; This can be an Integer or a String.
		 */
		private Object state;

		/**
		 * @return true if this node is one of the two terminal nodes
		 */
		private boolean isLeaf() {
			return this == nodeF || this == nodeT;
		}

		/**
		 * @return the number of sons that are different from the False terminal node
		 */
		public int nRelevantSons() {
			return nRelevantSons != null ? nRelevantSons : (nRelevantSons = (int) Stream.of(sons).filter(c -> c != nodeF).count());
		}

		/**
		 * Returns the number of internal nodes (i.e., other than terminal ones) that can be reached from this node. Nodes whose id is in the specifies set must
		 * be ignored (because already counted)
		 * 
		 * @param set
		 *            the ids of nodes that must ignored
		 * @return the number of internal nodes that can be reached from this node
		 */
		private int nInternalNodes(Set<Integer> set) {
			if (isLeaf() || set.contains(num))
				return 0; // static leaves are not counted here and nodes with id already in set are already counted
			set.add(num);
			return 1 + Stream.of(sons).mapToInt(c -> c.nInternalNodes(set)).sum();
		}

		/**
		 * Builds a node for the MDD at the specified level
		 * 
		 * @param level
		 *            a level in the MDD
		 */
		private Node(int level) {
			this.num = nCreatedNodes++;
			this.level = level; // this is -1 for the two special terminal nodes
		}

		/**
		 * Builds a node for the MDD at the specified level. For each value index of the domain of the associated variable, there is a son. If stars are managed
		 * apart, there is additionally one special son.
		 * 
		 * @param level
		 *            a level in the MDD
		 * @param nSons
		 *            the number of possible classical branches (one for each value index)
		 * @param starred
		 *            indicates if an additional son must be added for '*'
		 * @param defaultNodeF
		 *            if true, the default target of each son is nodeF, otherwise nodeT
		 */
		private Node(int level, int nSons, boolean starred, boolean defaultNodeF) {
			this(level);
			this.starred = starred;
			this.sons = IntStream.range(0, nSons + (starred ? 1 : 0)).mapToObj(i -> defaultNodeF ? nodeF : nodeT).toArray(Node[]::new); // + 1 for STAR

		}

		private Node(int level, int nSons, boolean starred, boolean defaultNodeF, Object state) {
			this(level, nSons, starred, defaultNodeF);
			this.state = state;
		}

		private void addTuple(int level, int index, int[] tuple, boolean positive, int[] domSizes) {
			Node son = sons[index];
			if (!son.isLeaf())
				son.addTuple(level + 1, tuple, positive, domSizes);
			else if (level == tuple.length - 1)
				sons[index] = positive ? nodeT : nodeF;
			else
				(sons[index] = new Node(level + 1, domSizes[level + 1], starred, positive)).addTuple(level + 1, tuple, positive, domSizes);
		}

		private void addTuple(int level, int[] tuple, boolean positive, int[] domSizes) {
			if (tuple[level] == Constants.STAR) {
				if (starred)
					addTuple(level, sons.length - 1, tuple, positive, domSizes); // for STAR, the special value index is sons.length-1
				else
					for (int i = 0; i < sons.length; i++)
						addTuple(level, i, tuple, positive, domSizes);
			} else
				addTuple(level, tuple[level], tuple, positive, domSizes);
		}

		/**
		 * Adds the specified tuple to the MDD
		 * 
		 * @param tuple
		 *            a tuple to be added to the MDD
		 * @param positive
		 *            indicates if the tuple is a support or a conflict
		 * @param domSizes
		 *            the size of the domains at each level
		 */
		public void addTuple(int[] tuple, boolean positive, int[] domSizes) {
			addTuple(0, tuple, positive, domSizes);
		}

		private boolean canReachNodeT(Set<Integer> reachingNodes, Set<Integer> unreachingNodes) {
			if (this == nodeT || reachingNodes.contains(num))
				return true;
			if (this == nodeF || unreachingNodes.contains(num))
				return false;
			boolean found = false;
			for (int i = 0; i < sons.length; i++)
				if (!sons[i].canReachNodeT(reachingNodes, unreachingNodes))
					sons[i] = nodeF; // note that we update some nodes
				else
					found = true;
			if (found)
				reachingNodes.add(num);
			else
				unreachingNodes.add(num);
			return found;
		}

		/**
		 * Builds the equivalence classes of the sons of the node
		 */
		private void buildSonsClasses() {
			if (isLeaf() || classes != null)
				return; // already built
			boolean discardClassForNodeF = true; // hard coding (to be replaced by a solver option?)
			Map<Node, List<Integer>> map = IntStream.range(0, sons.length).filter(i -> !discardClassForNodeF || sons[i] != nodeF).boxed()
					.collect(Collectors.groupingBy(i -> sons[i]));
			classes = map.values().stream().map(list -> Kit.intArray(list)).toArray(int[][]::new);
			for (Node son : sons)
				son.buildSonsClasses();
		}

		public boolean canReachNodeT() {
			return canReachNodeT(new HashSet<Integer>(), new HashSet<Integer>());
		}

		private int renameNodes(int lastId, Map<Integer, Node> map) {
			if (isLeaf() || map.get(num) == this)
				return lastId;
			lastId++;
			map.put(num = lastId, this);
			for (Node son : sons)
				lastId = son.renameNodes(lastId, map);
			// for (int i = 0; i < classes.length; i++) lastId = sons[classes[i][0]].renameNodes(lastId, map); // alternative
			return lastId;
		}

		private boolean controlUniqueNodes(Map<Integer, Node> map) {
			Node node = map.get(num);
			if (node == null)
				map.put(num, this);
			else
				control(node == this, () -> "two nodes with the same id in the MDD " + num);
			return sons == null || Stream.of(sons).noneMatch(child -> !child.controlUniqueNodes(map));
		}

		private int finalizeRoot() {
			control(level == 0); // must be called on a root
			canReachNodeT(new HashSet<Integer>(), new HashSet<Integer>()); // if root built from transitions, necessary ?
			buildSonsClasses();
			int nNodes = renameNodes(1, new HashMap<Integer, Node>()) + 1;
			// System.out.println("MDD : nNodes=" + nNodes + " nBuiltNodes=" + Node.nCreatedNodes);
			display();
			assert controlUniqueNodes(new HashMap<Integer, Node>());
			// buildSplitter();
			return nNodes;
		}

		private Node recursiveReduction(Map<IntArrayHashKey, Node> reductionMap) {
			if (isLeaf())
				return this;
			for (int i = 0; i < sons.length; i++)
				sons[i] = sons[i].recursiveReduction(reductionMap);
			IntArrayHashKey hk = new IntArrayHashKey(Stream.of(sons).mapToInt(c -> c.num).toArray());
			return reductionMap.computeIfAbsent(hk, k -> this);
		}

		private void display(int[] cnts, boolean displayClasses) {
			if (this.isLeaf())
				return;
			Kit.log.fine(num + "@" + level + " => ");
			if (cnts != null)
				cnts[level]++;
			if (sons == null)
				return;
			Kit.log.fine("{" + Stream.of(sons).map(child -> child.num + "").collect(Collectors.joining(",")) + "}");
			if (displayClasses) {
				if (classes != null)
					for (int i = 0; i < classes.length; i++)
						Kit.log.fine("class " + i + " => {" + Kit.join(classes[i]) + "}");
				Kit.log.fine("nSonsNotNodeF=" + nRelevantSons);
			}
			// Stream.of(sons).filter(s -> s.num > num).forEach(s -> s.display(cnts, displayClasses));
		}

		public void display() {
			display(null, false);
		}

		public int displayTuples(Domain[] doms, int[] currTuple, int currLevel, int cnt) {
			if (this == nodeT) {
				Kit.log.info(Kit.join(currTuple));
				cnt++;
			}
			if (isLeaf())
				return cnt;
			for (int i = 0; i < sons.length; i++) {
				currTuple[currLevel] = starred && i == sons.length - 1 ? Constants.STAR : doms[currLevel].toVal(i);
				cnt = sons[i].displayTuples(doms, currTuple, currLevel + 1, cnt);
			}
			return cnt;
		}

		public void collectCompressedTuples(List<int[][]> list, int[][] m, int level) {
			if (this == nodeT)
				list.add(Stream.of(m).map(t -> t.clone()).toArray(int[][]::new));
			if (isLeaf())
				return;
			for (int i = 0; i < classes.length; i++) {
				m[level] = classes[i];
				Node representativeChild = sons[classes[i][0]];
				representativeChild.collectCompressedTuples(list, m, level + 1);
			}
		}

		public Node filter(int[][] values, int prevVal) {
			if (isLeaf())
				return this;
			// int left = -1;
			// for (int i = childs.length - 1; i >= 0; i--)
			// if (values[i] > prevVal && childs[i] != nodeF) {
			// left = i; break; }
			// MDDNode node = null;
			// if (left == -1) node = this;
			// else {
			Node node = new Node(level, sons.length, starred, true);
			for (int i = 0; i < sons.length; i++)
				if (values[level][i] <= prevVal)
					node.sons[i] = sons[i];
			// }
			for (int i = 0; i < sons.length; i++)
				node.sons[i] = node.sons[i].filter(values, values[level][i]);
			return node;
		}

		public String name() {
			return this == nodeF ? "nodeF" : this == nodeT ? "nodeT" : level == 0 ? "root" : "n" + num;
		}

		private class _Transition {
			String src;
			int val;
			String dst;

			_Transition(String src, int val, String dst) {
				this.src = src;
				this.val = val;
				this.dst = dst;
			}
		}

		private List<_Transition> getTransitions(Domain[] doms, List<_Transition> transitions, Set<Node> processedNodes) {
			if (sons != null) {
				for (int i = 0; i < sons.length; i++)
					if (sons[i] != nodeF)
						transitions.add(new _Transition(name(), starred && i == sons.length - 1 ? Constants.STAR_INT : doms[level].toVal(i), sons[i].name()));
				processedNodes.add(this);
				for (Node son : sons)
					if (!processedNodes.contains(son))
						son.getTransitions(doms, transitions, processedNodes);
			}
			return transitions;
		}

		public String getTransitions(Domain[] doms) {
			StringBuilder sb = new StringBuilder("{\"transitions\":[");
			for (_Transition tr : getTransitions(doms, new ArrayList<>(), new HashSet<Node>()))
				sb.append("\n  [\"" + tr.src).append("\",").append(tr.val).append(",\"").append(tr.dst).append("\"],");
			sb.deleteCharAt(sb.length() - 1);
			sb.append("\n]\n}");
			return sb.toString();
		}
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	private boolean checkWhenStarred(int[] t, int level, Node node) {
		if (node == nodeT)
			return true;
		if (node == nodeF)
			return false;
		return checkWhenStarred(t, level + 1, node.sons[t[level]]) || checkWhenStarred(t, level + 1, node.sons[node.sons.length - 1]);
	}

	@Override
	public boolean checkIndexes(int[] t) {
		if (root.starred)
			return checkWhenStarred(t, 0, root);
		Node node = root;
		for (int i = 0; !node.isLeaf(); i++)
			node = node.sons[t[i]];
		return node == nodeT;
	}

	/**
	 * The root node of the MDD
	 */
	public Node root;

	/**
	 * The arity of the MDD
	 */
	public final int arity;

	/**
	 * The number of nodes in the MDD (used as a cache)
	 */
	private Integer nNodes;

	/**
	 * @return the number of nodes in the MDD
	 */
	public Integer nNodes() {
		return nNodes != null ? nNodes : (nNodes = 2 + root.nInternalNodes(new HashSet<Integer>()));
	}

	public MDD(CMDD c) {
		super(c);
		this.arity = c.scp.length;
	}

	public MDD(CMDD c, Node root) {
		this(c);
		this.root = root;
		control(root.starred == (c instanceof CMDDS));
	}

	public MDD(CMDDO c, Automaton automaton) {
		this(c);
		this.root = Node.buildRootFromAutomaton(automaton, c.doms);
	}

	public MDD(CMDDO c, Transition[] transitions) {
		this(c);
		this.root = Node.buildRootFromTransitions(transitions, c.doms);
	}

	public MDD(CMDDO c, int[] coeffs, Object limits) {
		this(c);
		this.root = Node.buildRootFromKnapsack(coeffs, limits, Variable.initDomainValues(c.scp));
		// displayTuples();
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		control(positive && tuples.length > 0);
		Constraint c = firstRegisteredCtr();
		this.root = Node.buildRootFromTuples(tuples, positive, c.doms, c instanceof CMDDS, true); // last parameter: using a solver option?
	}

	public void displayTuples() {
		Domain[] doms = Stream.of(firstRegisteredCtr().scp).map(x -> x.dom).toArray(Domain[]::new);
		int cnt = root.displayTuples(doms, new int[doms.length], 0, 0);
		Kit.log.info(" => " + cnt + " tuples");
	}

	/**********************************************************************************************
	 * Start of experimental section (splitting - compression)
	 *********************************************************************************************/

	private final class MDDSplitter {

		private final int[] splitMode;

		private final int[][][] splitTuples;

		private Set<int[]>[] splitSets; // used during collecting tuples

		private Map<Integer, Integer>[] auxiliaryLevelMaps;

		private MDDSplitter(int[] initialSplitMode) {
			this.splitMode = initialSplitMode;
			// assert Kit.sum(initialSplitMode) == mdd.firstRegisteredCtr().scp.length;
			for (int i = 0; i < splitMode.length; i++)
				if (i == 0 || i == splitMode.length - 1)
					splitMode[i] += 1; // because one additional variable
				else
					splitMode[i] += 2; // because two additional variables
			this.splitSets = IntStream.range(0, initialSplitMode.length).mapToObj(i -> new TreeSet<>(Utilities.lexComparatorInt)).toArray(Set[]::new);
			this.auxiliaryLevelMaps = IntStream.range(0, initialSplitMode.length - 1).mapToObj(i -> new HashMap<>()).toArray(Map[]::new);

			split2(root, 0);
			this.splitTuples = new int[splitSets.length][][];
			for (int i = 0; i < splitTuples.length; i++) {
				splitTuples[i] = splitSets[i].toArray(new int[splitSets[i].size()][]);
				splitSets[i].clear();
				splitSets[i] = null;
			}
			for (int i = 0; i < splitTuples.length; i++)
				System.out.println("i=" + i + " size=" + splitTuples[i].length);
		}

		private int getAuxiliaryLevelNodeId(int nodeId, int splitLevel) {
			return auxiliaryLevelMaps[splitLevel].computeIfAbsent(nodeId, k -> auxiliaryLevelMaps[splitLevel].size());
		}

		private void getTuples(Node node, int splitLevel, int[] currentTuple, int currentLevel, int stoppingLevel) {
			if (node == nodeF)
				return;
			if (stoppingLevel == -1) {
				if (node == nodeT)
					splitSets[splitLevel].add(currentTuple.clone());
				else
					for (int i = 0; i < node.sons.length; i++) {
						currentTuple[currentLevel] = i;
						getTuples(node.sons[i], splitLevel, currentTuple, currentLevel + 1, stoppingLevel);
					}
			} else {
				assert node != nodeT && stoppingLevel != -1;
				if (currentLevel == stoppingLevel) {
					currentTuple[currentLevel] = getAuxiliaryLevelNodeId(node.num, splitLevel);
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

		public void split2(Node startingNode, int splitLevel) {
			int[] currentTuple = new int[splitMode[splitLevel]];
			int currentLevel = 0;
			if (splitLevel > 0)
				currentTuple[currentLevel++] = getAuxiliaryLevelNodeId(startingNode.num, splitLevel - 1);
			getTuples(startingNode, splitLevel, currentTuple, currentLevel, (splitLevel == splitSets.length - 1 ? -1 : splitMode[splitLevel] - 1));
		}

	}

	private boolean mustBuildSplitter = false;

	public MDDSplitter splitter;

	void buildSplitter() {
		if (mustBuildSplitter) {
			int arity = firstRegisteredCtr().scp.length;
			splitter = new MDDSplitter(new int[] { (int) Math.ceil(arity / 2.0), (int) Math.floor(arity / 2.0) });
		}
	}

	public int[][][] toCompressedTable() {
		// root.buildSonsClasses();
		LinkedList<int[][]> list = new LinkedList<>();
		root.collectCompressedTuples(list, new int[firstRegisteredCtr().scp.length][], 0);
		return list.stream().toArray(int[][][]::new);
	}

	@SuppressWarnings("unused")
	public static void main(String[] args) {
		int length = Integer.parseInt(args[0]);
		// buildFromAutomata(2, new int[][] { { 1, 2 }, { -1, 3 }, { 3, -1 }, { 3, 4 }, { -1, -1 } }, 0, new int[] { 4
		// }, 5);
		// Automata automata = new Automata(10, 2, new int[][] { { 0, 0, 1 }, { 0, 1, 2 }, { 1, 1, 3 }, { 2, 0, 3 }, {
		// 3, 0, 3 }, { 3, 1, 4
		// } }, 0, new int[] {
		// 4 });
		// Automata automata = null;
		// automata = new Automata(10, 3, new int[][] { { 0, 0, 1 }, { 0, 2, 2 }, { 1, 0, 3 }, { 2, 2, 4 }, { 3, 0, 5 },
		// { 3, 1, 7 }, { 4,
		// 1, 7 }, { 4, 2, 6 },
		// { 5, 1, 7 }, { 6, 1, 7 },
		// { 7, 1, 8 }, { 8, 0, 1 }, { 8, 1, 9 }, { 8, 2, 2 }, { 9, 0, 1 }, { 9, 2, 2 } }, 0, new int[] { 3, 4, 5, 6, 8,
		// 9 });
		// automata = new Automata(7, 4, new int[][] { { 0, 0, 0 }, { 0, 1, 1 }, { 0, 2, 2 }, { 0, 3, 3 }, { 1, 0, 4 },
		// { 1, 1, 1 }, { 2, 0,
		// 5 }, { 2, 2, 2 }, {
		// 3, 0, 6 }, { 3, 3, 3 },
		// { 4, 0, 4 }, { 4, 1, 1 }, {4,2,2}, { 5, 0, 5 }, { 5, 2, 2 }, {5,3,3}, { 6, 0, 6 }, { 6, 3, 3 } ,{6,1,1}}, 0,
		// new int[] { 0, 1, 2,
		// 3, 4, 5,6 });

		// automata = new Automata(5, 2, new int[][] { { 0, 0, 0 }, { 0, 1, 1 }, { 1, 1, 2 }, { 2, 0, 3 }, { 3, 0, 3 },
		// { 3, 1, 4 }, { 4, 0,
		// 4 } }, 0, new int[]
		// { 4 });
		// MDD m = new MDD(null).storeTuples(automata, length);

		// MDD m = new MDD(null).storeTuplesFromKnapsack(70,82,new int[] {27,37,45,53} , new int[] {0,1,2,3});
		// MDD m = new MDD(null).storeTuplesFromKnapsack(34,34, Kit.buildIntArrayWithUniqueValue(4, 1) ,
		// Kit.buildIntArray(16, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(65,65, Kit.buildIntArrayWithUniqueValue(5, 1) ,
		// Kit.buildIntArray(25, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(111,111, Kit.buildIntArrayWithUniqueValue(6, 1) ,
		// Kit.buildIntArray(36, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(175,175, Kit.buildIntArrayWithUniqueValue(7, 1) ,
		// Kit.buildIntArray(49, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(505,505, Kit.buildIntArrayWithUniqueValue(10, 1) ,
		// Kit.buildIntArray(100, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(1379,1379, Kit.buildIntArrayWithUniqueValue(14, 1) ,
		// Kit.buildIntArray(196, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(Kit.repeat(1, 20), new Range(4010, 4010), Kit.range(1, 400));
		// m.root.display();
	}
}

// if (!directEncodingFromAutomata) buildSubtree root.buildSubtree(nbLetters, transitions, finalStates, height + 1, 0,
// new
// HashMap<IntArrayHashKey,
// MDDNode>(2000));

// public static void storeTuples1(int nbStates, int nbLetters, int[][] transitions, int initialState, int[]
// finalStates, int nbLevels) {
// control(nbLevels > 1);
// Map<Integer, MDDNode> map = new HashMap<Integer, MDDNode>();
// MDDNode root = new MDDNode(this,0, false, nbLetters); // TODO a virer la declaertaionxxxxxxxxxxxxxxxxxxxxxxxxxxx
// List<MDDNode> listOfNodesAtCurrentLevel = new ArrayList<MDDNode>(), nextList = new ArrayList<MDDNode>();
// listOfNodesAtCurrentLevel.add(root);
// root.state = initialState;
// for (int level = 0; level < nbLevels - 1; level++) {
// nextList.clear();
// for (MDDNode node : listOfNodesAtCurrentLevel) {
// map.clear();
// for (int letter = 0; letter < nbLetters; letter++) {
// int nextState = transitions[node.state][letter];
// if (nextState == -1)
// continue;
// if (level == nbLevels - 2) {
// if (Kit.isArrayContaining(finalStates, nextState)) {
// node.setChild(letter, MDDNode.nodeTT);
// }
// continue;
// }
// MDDNode nextNode = map.get(nextState);
// if (nextNode == null) {
// nextNode = new MDDNode(this,level + 1, true, nbLetters);
// nextNode.state = nextState;
// map.put(nextState, nextNode);
// nextList.add(nextNode);
// }
// node.setChild(letter, nextNode);
// }
// }
// List<MDDNode> tmp = listOfNodesAtCurrentLevel;
// listOfNodesAtCurrentLevel = nextList;
// nextList = tmp;
// }
// root.display(null);
// }

// private static boolean buildSubtree(MDDNode node, int nbLetters, int[][] transitions, int[] finalStates, int
// nbLevels, int level) {
// boolean found = false;
// Map<Integer, MDDNode> map = new HashMap<Integer, MDDNode>();
// for (int letter = 0; letter < nbLetters; letter++) {
// int nextState = transitions[node.state][letter];
//
// boolean trueNode = false;
// if (level == nbLevels - 2) {
// trueNode = nextState != -1 && Kit.isArrayContaining(finalStates, nextState);
// node.setChild(letter, trueNode ? MDDNode.nodeTT : MDDNode.nodeFF);
// } else {
// MDDNode nextNode = map.get(nextState);
// if (nextNode == null) {
// nextNode = new MDDNode(this,level + 1, true, nbLetters);
// nextNode.state = nextState;
// map.put(nextState, nextNode);
// }
// trueNode = nextState != -1 && buildSubtree(nextNode, nbLetters, transitions, finalStates, nbLevels, level + 1);
// node.setChild(letter, trueNode ? nextNode : MDDNode.nodeFF);
// }
//
// found = found || trueNode;
// }
//
//
// /*
// * MDDNode[] childs = node.getChilds(); int[] t = new int[childs.length]; for (int i = 0; i < childs.length; i++) t[i]
// =
// childs[i].getId(); IntArrayHashKey hk
// = new IntArrayHashKey(t); MDDNode
// identicalNode =
// * reductionMapBisTmp.get(hk); if (identicalNode == null) { reductionMapBisTmp.put(hk, node); return node; } else
// return identicalNode;
// */
//
// return found;
// }
