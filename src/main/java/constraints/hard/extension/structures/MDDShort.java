/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension.structures;

import static org.xcsp.common.Constants.STAR;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.stream.Stream;

import org.xcsp.common.Constants;

import constraints.Constraint;
import constraints.hard.extension.CtrExtensionMDDShort;
import utility.Kit;
import utility.Kit.IntArrayHashKey;
import variables.Variable;

public final class MDDShort extends ExtensionStructureHard {

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

	public MDDShort(CtrExtensionMDDShort c) {
		super(c);
	}

	public MDDShort(CtrExtensionMDDShort c, MDDNodeShort root) {
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
