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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Range;
import org.xcsp.common.Utilities;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Transition;

import constraints.Constraint;
import constraints.extension.ExtensionMDD;
import utility.Kit;
import utility.Kit.IntArrayHashKey;
import variables.Variable;
import variables.domains.Domain;

public final class MDD extends ExtensionStructure {

	public MDDNode root;

	private Integer nNodes;

	private boolean reductionWhileProcessingTuples = false; // hard coding

	private int nCreatedNodes = 2; // because two two first pre-built nodes nodeF and nodeT

	public Integer nNodes() {
		return nNodes != null ? nNodes : (nNodes = 2 + root.nInternalNodes(new HashSet<Integer>()));
	}

	public int nextNodeId() {
		return nCreatedNodes++;
	}

	public MDD(ExtensionMDD c) {
		super(c);
	}

	public MDD(ExtensionMDD c, MDDNode root) {
		this(c);
		this.root = root;
	}

	public MDD(ExtensionMDD c, Automaton automata) {
		this(c);
		storeTuplesFromAutomata(automata, c.scp.length, Stream.of(c.scp).map(x -> x.dom).toArray(Domain[]::new));
	}

	public MDD(ExtensionMDD c, Object[][] transitions) {
		this(c);
		storeTuplesFromTransitions(transitions, Stream.of(c.scp).map(x -> x.dom).toArray(Domain[]::new));
	}

	public MDD(ExtensionMDD c, int[] coeffs, Object limits) {
		this(c);
		// Kit.control(Variable.haveSameDomainType(c.scp));
		// int[] values = IntStream.range(0, c.scp[0].dom.initSize()).map(i -> c.scp[0].dom.toVal(i)).toArray();
		storeTuplesFromKnapsack(coeffs, limits, Variable.initDomainValues(c.scp));
	}

	private MDDNode recursiveReduction(MDDNode node, Map<IntArrayHashKey, MDDNode> reductionMap) {
		if (node.isLeaf())
			return node;
		for (int i = 0; i < node.sons.length; i++)
			node.sons[i] = recursiveReduction(node.sons[i], reductionMap);
		IntArrayHashKey hk = new IntArrayHashKey(Stream.of(node.sons).mapToInt(c -> c.id).toArray());
		return reductionMap.computeIfAbsent(hk, k -> node);
	}

	private void reduce(int[] prevTuple, int[] currTuple, Map<IntArrayHashKey, MDDNode> reductionMap) {
		int i = 0;
		MDDNode node = root;
		while (prevTuple[i] == currTuple[i])
			node = node.sons[prevTuple[i++]];
		// assuming that tuples come in lex ordering, we can definitively reduce the left branch
		node.sons[prevTuple[i]] = recursiveReduction(node.sons[prevTuple[i]], reductionMap);
	}

	private void finalizeStoreTuples() {
		root.buildSonsClasses();
		nNodes = root.renameNodes(1, new HashMap<Integer, MDDNode>()) + 1;
		Kit.log.info("MDD : nNodes=" + nNodes + " nBuiltNodes=" + nCreatedNodes);
		assert root.controlUniqueNodes(new HashMap<Integer, MDDNode>());
		// buildSplitter();
		// root.display();
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		Kit.control(positive && tuples.length > 0);
		Constraint ctr = firstRegisteredCtr();
		int[] domainSizes = Variable.domSizeArrayOf(ctr.scp, true);
		Map<IntArrayHashKey, MDDNode> reductionMap = new HashMap<>(2000);
		this.root = new MDDNode(this, 0, domainSizes[0], positive);
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

	public MDD storeTuplesFromTransitions(Object[][] transitions, Domain[] domains) {
		Map<String, MDDNode> nodes = new HashMap<>();
		Set<String> possibleRoots = new HashSet<>(), notRoots = new HashSet<>();
		Set<String> possibleWells = new HashSet<>(), notWells = new HashSet<>();
		for (Object[] tr : transitions) {
			String src = (String) tr[0], tgt = (String) tr[2];
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
		Kit.control(possibleRoots.size() == 1 && possibleWells.size() == 1,
				() -> "sizes= " + possibleRoots.size() + " " + possibleWells.stream().collect(Collectors.joining(" ")));
		String sroot = possibleRoots.toArray(new String[1])[0];
		String swell = possibleWells.toArray(new String[1])[0];
		nodes.put(sroot, root = new MDDNode(this, 0, domains[0].initSize(), true));
		nodes.put(swell, MDDNode.nodeT);
		// TODO reordering transitions to guarantee that the src node has already been generated
		for (Object[] tr : transitions) {
			MDDNode node1 = nodes.get(tr[0]);
			long v = tr[1] instanceof Integer ? (Integer) tr[1] : (Long) tr[1];
			int val = Utilities.safeInt(v);
			int idx = domains[node1.level].toIdx(val);
			Kit.control(idx != -1);
			MDDNode node2 = nodes.computeIfAbsent((String) tr[2], k -> new MDDNode(this, node1.level + 1, domains[node1.level + 1].initSize(), true));
			// MDDNode node2 = nodes.get(tr[2]);
			// if (node2 == null)
			// nodes.put((String) tr[2], node2 = new MDDNode(this, node1.level + 1, domains[node1.level + 1].initSize(), true));
			node1.sons[idx] = node2;
		}
		// root.canReachNodeT();
		finalizeStoreTuples();
		return this;
	}

	private Map<String, List<Transition>> buildNextTransitions(Automaton automata) {
		Map<String, List<Transition>> map = new HashMap<>();
		map.put(automata.startState, new ArrayList<>());
		Stream.of(automata.finalStates).forEach(s -> map.put(s, new ArrayList<>()));
		Stream.of(automata.transitions).forEach(t -> {
			map.put(t.firstState, new ArrayList<>());
			map.put(t.secondState, new ArrayList<>());
		});
		Stream.of(automata.transitions).forEach(t -> map.get(t.firstState).add(t));
		return map;
	}

	public MDD storeTuplesFromAutomata(Automaton automata, int arity, Domain[] domains) {
		Kit.control(arity > 1 && IntStream.range(1, domains.length).allMatch(i -> domains[i].typeIdentifier() == domains[0].typeIdentifier()));
		Map<String, List<Transition>> nextTrs = buildNextTransitions(automata);
		this.root = new MDDNode(this, 0, domains[0].initSize(), true, automata.startState);
		Map<String, MDDNode> prevs = new HashMap<>(), nexts = new HashMap<>();
		prevs.put((String) root.state, root);
		for (int i = 0; i < arity; i++) {
			for (MDDNode node : prevs.values()) {
				for (Transition tr : nextTrs.get(node.state)) {
					int v = Utilities.safeInt((Long) tr.symbol);
					int a = domains[i].toIdx(v);
					if (a != -1) {
						String nextState = tr.secondState;
						if (i == arity - 1) {
							node.sons[a] = Utilities.indexOf(nextState, automata.finalStates) != -1 ? MDDNode.nodeT : MDDNode.nodeF;
						} else {
							// MDDNode nextNode = nexts.computeIfAbsent(nextState, k -> new MDDNode(this, i + 1, domains[i].initSize(), true,
							// nextState)); // pb with i not final
							MDDNode nextNode = nexts.get(nextState);
							if (nextNode == null)
								nexts.put(nextState, nextNode = new MDDNode(this, i + 1, domains[i].initSize(), true, nextState));
							node.sons[a] = nextNode;
						}
					}
				}
			}
			Map<String, MDDNode> tmp = prevs;
			prevs = nexts;
			nexts = tmp;
			nexts.clear();
		}
		root.canReachNodeT();
		finalizeStoreTuples();
		return this;
	}

	// coeffs, and limits (either a Range or an int array) from the knapsack constraint, and values are the possible values at each level
	public MDD storeTuplesFromKnapsack(int[] coeffs, Object limits, int[][] values) {
		this.root = new MDDNode(this, 0, values[0].length, true, 0);
		Map<Integer, MDDNode> prevs = new HashMap<>(), nexts = new HashMap<>();
		prevs.put((Integer) root.state, root);
		for (int level = 0; level < coeffs.length; level++) {
			for (MDDNode node : prevs.values()) {
				for (int j = 0; j < values[level].length; j++) {
					int nextState = (Integer) node.state + coeffs[level] * values[level][j];
					if (level == coeffs.length - 1) {
						if (limits instanceof Range)
							node.sons[j] = ((Range) limits).contains(nextState) ? MDDNode.nodeT : MDDNode.nodeF;
						else
							node.sons[j] = Utilities.indexOf(nextState, (int[]) limits) != -1 ? MDDNode.nodeT : MDDNode.nodeF;
					} else {
						MDDNode nextNode = nexts.get(nextState);
						if (nextNode == null)
							nexts.put(nextState, nextNode = new MDDNode(this, level + 1, values[level + 1].length, true, nextState));
						node.sons[j] = nextNode;
					}
				}
			}
			Map<Integer, MDDNode> tmp = prevs;
			prevs = nexts;
			nexts = tmp;
			nexts.clear();
		}
		root.canReachNodeT();

		boolean increasing = false;
		if (!increasing) {
			finalizeStoreTuples();
			// displayTuples();
		} else {
			root = root.filter(values, Integer.MAX_VALUE);
			recursiveReduction(root, new HashMap<>(2000));
			finalizeStoreTuples();
			root.display();
			displayTuples();
		}
		return this;
	}

	@Override
	public boolean checkIdxs(int[] t) {
		MDDNode node = root;
		for (int i = 0; !node.isLeaf(); i++)
			node = node.sons[t[i]];
		return node == MDDNode.nodeT;
	}

	public void displayTuples() {
		int cnt = root.displayTuples(Variable.buildDomainsArrayFor(firstRegisteredCtr().scp), new int[firstRegisteredCtr().scp.length], 0, 0);
		Kit.log.info(" => " + cnt + " tuples");
	}

	/**********************************************************************************************
	 * Start of experimental section (splitting - compression)
	 *********************************************************************************************/

	private boolean mustBuildSplitter = false;

	private MDDSplitter splitter;

	public MDDSplitter getSplitter() {
		return splitter;
	}

	void buildSplitter() {
		if (mustBuildSplitter) {
			int arity = firstRegisteredCtr().scp.length;
			splitter = new MDDSplitter(this, new int[] { (int) Math.ceil(arity / 2.0), (int) Math.floor(arity / 2.0) });
		}
	}

	public int[][][] buildCompressedTable() {
		// root.buildChildClasses();
		Constraint ctr = firstRegisteredCtr();
		LinkedList<int[][]> list = new LinkedList<>();
		root.collectCompressedTuples(list, new int[ctr.scp.length][], 0);
		int[][][] compressedTuples = Kit.intArray3D(list);
		return compressedTuples;
	}

	@SuppressWarnings("unused")
	public static void main(String[] args) {
		int length = Integer.parseInt(args[0]);
		// buildFromAutomata(2, new int[][] { { 1, 2 }, { -1, 3 }, { 3, -1 }, { 3, 4 }, { -1, -1 } }, 0, new int[] { 4 }, 5);
		// Automata automata = new Automata(10, 2, new int[][] { { 0, 0, 1 }, { 0, 1, 2 }, { 1, 1, 3 }, { 2, 0, 3 }, { 3, 0, 3 }, { 3, 1, 4
		// } }, 0, new int[] {
		// 4 });
		// Automata automata = null;
		// automata = new Automata(10, 3, new int[][] { { 0, 0, 1 }, { 0, 2, 2 }, { 1, 0, 3 }, { 2, 2, 4 }, { 3, 0, 5 }, { 3, 1, 7 }, { 4,
		// 1, 7 }, { 4, 2, 6 },
		// { 5, 1, 7 }, { 6, 1, 7 },
		// { 7, 1, 8 }, { 8, 0, 1 }, { 8, 1, 9 }, { 8, 2, 2 }, { 9, 0, 1 }, { 9, 2, 2 } }, 0, new int[] { 3, 4, 5, 6, 8, 9 });
		// automata = new Automata(7, 4, new int[][] { { 0, 0, 0 }, { 0, 1, 1 }, { 0, 2, 2 }, { 0, 3, 3 }, { 1, 0, 4 }, { 1, 1, 1 }, { 2, 0,
		// 5 }, { 2, 2, 2 }, {
		// 3, 0, 6 }, { 3, 3, 3 },
		// { 4, 0, 4 }, { 4, 1, 1 }, {4,2,2}, { 5, 0, 5 }, { 5, 2, 2 }, {5,3,3}, { 6, 0, 6 }, { 6, 3, 3 } ,{6,1,1}}, 0, new int[] { 0, 1, 2,
		// 3, 4, 5,6 });

		// automata = new Automata(5, 2, new int[][] { { 0, 0, 0 }, { 0, 1, 1 }, { 1, 1, 2 }, { 2, 0, 3 }, { 3, 0, 3 }, { 3, 1, 4 }, { 4, 0,
		// 4 } }, 0, new int[]
		// { 4 });
		// MDD m = new MDD(null).storeTuples(automata, length);

		// MDD m = new MDD(null).storeTuplesFromKnapsack(70,82,new int[] {27,37,45,53} , new int[] {0,1,2,3});
		// MDD m = new MDD(null).storeTuplesFromKnapsack(34,34, Kit.buildIntArrayWithUniqueValue(4, 1) , Kit.buildIntArray(16, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(65,65, Kit.buildIntArrayWithUniqueValue(5, 1) , Kit.buildIntArray(25, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(111,111, Kit.buildIntArrayWithUniqueValue(6, 1) , Kit.buildIntArray(36, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(175,175, Kit.buildIntArrayWithUniqueValue(7, 1) , Kit.buildIntArray(49, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(505,505, Kit.buildIntArrayWithUniqueValue(10, 1) , Kit.buildIntArray(100, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(1379,1379, Kit.buildIntArrayWithUniqueValue(14, 1) , Kit.buildIntArray(196, 1));
		// MDD m = new MDD(null).storeTuplesFromKnapsack(Kit.repeat(1, 20), new Range(4010, 4010), Kit.range(1, 400));
		// m.root.display();
		// Kit.prn(" => " + m.root.displayTuples(new int[length], 0, 0) + " tuples");
	}
}

// if (!directEncodingFromAutomata) buildSubtree root.buildSubtree(nbLetters, transitions, finalStates, height + 1, 0, new
// HashMap<IntArrayHashKey,
// MDDNode>(2000));

// public static void storeTuples1(int nbStates, int nbLetters, int[][] transitions, int initialState, int[] finalStates, int nbLevels) {
// Kit.control(nbLevels > 1);
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

// private static boolean buildSubtree(MDDNode node, int nbLetters, int[][] transitions, int[] finalStates, int nbLevels, int level) {
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
// * MDDNode[] childs = node.getChilds(); int[] t = new int[childs.length]; for (int i = 0; i < childs.length; i++) t[i] =
// childs[i].getId(); IntArrayHashKey hk
// = new IntArrayHashKey(t); MDDNode
// identicalNode =
// * reductionMapBisTmp.get(hk); if (identicalNode == null) { reductionMapBisTmp.put(hk, node); return node; } else return identicalNode;
// */
//
// return found;
// }
