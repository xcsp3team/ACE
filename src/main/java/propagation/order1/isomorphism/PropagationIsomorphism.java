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
package propagation.order1.isomorphism;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;

import constraints.Constraint;
import constraints.CtrHard;
import propagation.order1.AC;
import search.Solver;
import utility.Kit;
import utility.Kit.IntLongPairReverse;
import utility.operations.GraphSimpleUndirected;
import variables.Variable;
import variables.domains.Domain;

public class PropagationIsomorphism extends AC {

	private final int NB_MIN_TURNS = 3;
	private final int NB_MAX_STORED_MATRICES = 50;

	private GraphSimpleUndirected initialPatternGraph, initialTargetGraph;

	private long[][][] patternMatrices, targetMatrices;

	private boolean useNeighbors1 = true, useNeighbors2 = false, useNeighbors1And2 = false, useMultiset = true;

	private NeighborhoodReasoning neighbors1, neighbors2, neighbors1And2;

	private long[] patternMultiset;
	private long[][] targetsMultiset;

	private int[] first, last, fixed, nbLasts, fixedPatternNeighbors;

	private boolean trace = false; // true;

	private boolean mustComputePattern = true, mustComputeTarget = true;

	private Domain[] domains; // of all variables

	private class NeighborhoodReasoning {
		private class Neighbors {
			private IntLongPairReverse[] nodes;

			private Neighbors(int[] indices) {
				this.nodes = IntStream.range(0, indices.length).mapToObj(i -> new IntLongPairReverse(indices[i])).toArray(IntLongPairReverse[]::new);
			}

			private void recordAndSort(long[] adjacentScores) {
				for (IntLongPairReverse node : nodes)
					node.value = adjacentScores[node.index];
				Arrays.sort(nodes);
			}

			private int findDominanceSupportFor(IntLongPairReverse node, int from, int to, boolean first) {
				if (first) {
					for (int i = from; i < to; i++)
						if (node.value > nodes[i].value)
							return -1;
						else if (fixed[i] == -1 && domains[node.index].isPresent(nodes[i].index))
							return i;
				} else {
					for (int i = from; i > to; i--)
						if (node.value <= nodes[i].value && fixed[i] == -1 && domains[node.index].isPresent(nodes[i].index))
							return i;
				}
				return -1;
			}
		}

		private Neighbors[] patternsNeighbors, targetsNeighbors;

		private int nFixedPatternNeighbors;

		private NeighborhoodReasoning(int[][] patternNeighborSelection, int[][] targetNeighborSelection) {
			Kit.control(patternNeighborSelection.length == initialPatternGraph.nNodes && targetNeighborSelection.length == initialTargetGraph.nNodes);
			patternsNeighbors = new Neighbors[patternNeighborSelection.length];
			for (int i = 0; i < patternsNeighbors.length; i++)
				patternsNeighbors[i] = new Neighbors(patternNeighborSelection[i]);
			targetsNeighbors = new Neighbors[targetNeighborSelection.length];
			for (int i = 0; i < targetsNeighbors.length; i++)
				targetsNeighbors[i] = new Neighbors(targetNeighborSelection[i]);
			// Kit.prn(Kit.implode2D(patternNeighbours));
		}

		private void reconsiderTargetNodes(int[][] targetNeighborSelection) {
			for (int i = 0; i < targetsNeighbors.length; i++)
				targetsNeighbors[i] = new Neighbors(targetNeighborSelection[i]);
		}

		private void recordScores(long[][] patternAdjacence, long[][] targetAdjacence) {
			// if (mustComputePattern)
			for (int i = 0; i < patternsNeighbors.length; i++)
				patternsNeighbors[i].recordAndSort(patternAdjacence[i]);
			// if (mustComputeTarget)
			for (int i = 0; i < targetsNeighbors.length; i++)
				targetsNeighbors[i].recordAndSort(targetAdjacence[i]);
		}

		private boolean fix(int k, int v) {
			first[k] = last[k] = v;
			fixed[v] = k;
			fixedPatternNeighbors[nFixedPatternNeighbors++] = k;
			// Kit.prn("fix " + k + " " + patternNeighbors[k] + " " + last[k]); // + " " patternNeighbors[k] )
			return true;
		}

		private boolean isNeighborDominated(int i, int j) {
			IntLongPairReverse[] patternScores = patternsNeighbors[i].nodes, targetScores = targetsNeighbors[j].nodes;
			int nPatternNeighbors = patternsNeighbors[i].nodes.length, nbTargetNeighbors = targetsNeighbors[j].nodes.length;

			// Kit.prn("Test dominance " + i + " " +j + " NBPN=" + nbPatternNeighbors + " nbTN=" + nbTargetNeighbors) ;
			if (nPatternNeighbors > nbTargetNeighbors)
				return false;

			for (int k = 0; k < nPatternNeighbors; k++)
				if (patternScores[k].value > targetScores[k].value)
					return false;
			Arrays.fill(fixed, 0, nbTargetNeighbors, -1);
			Arrays.fill(nbLasts, 0, nbTargetNeighbors, 0);
			nFixedPatternNeighbors = 0;
			for (int k = 0; k < nPatternNeighbors; k++) {
				first[k] = targetsNeighbors[j].findDominanceSupportFor(patternScores[k], 0, nbTargetNeighbors, true);
				if (first[k] == -1)
					return false;
				last[k] = targetsNeighbors[j].findDominanceSupportFor(patternScores[k], nbTargetNeighbors - 1, first[k], false);
				if (last[k] == -1) {
					fix(k, first[k]);
				}
				nbLasts[last[k]]++;
			}
			while (true) {
				boolean newFixed = false;
				for (int k = 0; k < nPatternNeighbors; k++) {
					if (first[k] != last[k]) {
						int fixedLast = fixed[last[k]];
						if (fixed[first[k]] != -1) {
							first[k] = targetsNeighbors[j].findDominanceSupportFor(patternScores[k], first[k] + 1, last[k], true);
							if (first[k] == -1) {
								if (fixedLast != -1)
									return false;
								newFixed = fix(k, last[k]);
							}
						}
						if (fixedLast != -1) {
							nbLasts[last[k]]--;
							last[k] = targetsNeighbors[j].findDominanceSupportFor(patternScores[k], last[k] - 1, first[k], false);
							if (last[k] == -1) {
								newFixed = fix(k, first[k]);
							}
							nbLasts[last[k]]++;
						}
					}
				}
				if (!newFixed)
					break;
			}
			int sum = 0;
			for (int k = 0; k < nPatternNeighbors; k++) {
				sum += nbLasts[k];
				if (sum > k + 1)
					return false;
			}
			boolean test = true;
			// if (nbFixedPatternNeighbors > 1)
			// Kit.prn("nbFixed=" + nbFixedPatternNeighbors);
			if (test)
				for (int cnt1 = 0; cnt1 < nFixedPatternNeighbors; cnt1++) {
					for (int cnt2 = cnt1 + 1; cnt2 < nFixedPatternNeighbors; cnt2++) {
						int k1 = fixedPatternNeighbors[cnt1], k2 = fixedPatternNeighbors[cnt2];
						int ii = patternScores[k1].index, iii = patternScores[k2].index;
						if (initialPatternGraph.adjacency[ii][iii] == 0)
							continue;
						// Kit.prn("ii =" + ii + " iii=" + iii + " " + last[k1] + " " + last[k2]);
						int jj = targetScores[last[k1]].index;
						int jjj = targetScores[last[k2]].index;
						if (initialTargetGraph.adjacency[jj][jjj] == 0) {
							// Kit.prn("toto");
							return false;
						}
					}
				}
			return true;
		}

	}

	private List<int[]> computePatternEdges() {
		List<int[]> edges = new ArrayList<>();
		for (Constraint ctr : solver.pb.constraints)
			if (ctr.scp.length == 2)
				edges.add(new int[] { ctr.scp[0].num, ctr.scp[1].num });
		return edges;
	}

	private List<int[]> computeTargetEdges() {
		List<int[]> edges = new ArrayList<>();
		for (CtrHard c : hards)
			if (c.scp.length == 2) {
				c.tupleManager.firstValidTuple();
				c.tupleManager.overValidTuples(t -> {
					if (c.checkIndexes(t))
						edges.add(t.clone());
				});
				break;
			}
		return edges;
	}

	private void buildGraphs() {
		domains = Variable.buildDomainsArrayFor(solver.pb.variables);
		initialPatternGraph = new GraphSimpleUndirected(solver.pb.variables.length, computePatternEdges());
		initialTargetGraph = new GraphSimpleUndirected(domains[0].initSize(), computeTargetEdges());
		initialPatternGraph.computeNodesAtDistance1();
		initialTargetGraph.computeNodesAtDistance1();
		if (useNeighbors1)
			neighbors1 = new NeighborhoodReasoning(initialPatternGraph.nodesAtDistance1, initialTargetGraph.nodesAtDistance1);
		if (useNeighbors2)
			neighbors2 = new NeighborhoodReasoning(initialPatternGraph.computeNodesAtDistance2(), initialTargetGraph.computeNodesAtDistance2());
		if (useNeighbors1And2)
			neighbors1And2 = new NeighborhoodReasoning(initialPatternGraph.computeNodesAtDistance1And2(), initialTargetGraph.computeNodesAtDistance1And2());
		if (useMultiset) {
			patternMultiset = new long[initialPatternGraph.nNodes - 1];
			targetsMultiset = new long[initialTargetGraph.nNodes][initialTargetGraph.nNodes - 1];
		}
		patternMatrices = new long[NB_MAX_STORED_MATRICES][][];
		targetMatrices = new long[NB_MAX_STORED_MATRICES][][];
		first = new int[initialPatternGraph.nNodes];
		last = new int[initialPatternGraph.nNodes];
		fixed = new int[initialTargetGraph.nNodes];
		nbLasts = new int[initialTargetGraph.nNodes];
		fixedPatternNeighbors = new int[initialPatternGraph.nNodes];
	}

	private int modifyAdjacence() {
		Kit.control(solver.depth() == 0);
		int nbModifications = 0;
		long[][] m = initialTargetGraph.adjacency;
		for (int i = 0; i < m.length; i++)
			for (int j = i + 1; j < m[i].length; j++) {
				if (m[i][j] == 0)
					continue;
				boolean foundSupport = false;
				for (Constraint ctr : solver.pb.constraints)
					if (ctr.scp.length == 2) {
						if ((ctr.scp[0].dom.isPresent(i) && ctr.scp[1].dom.isPresent(j)) || (ctr.scp[0].dom.isPresent(j) && ctr.scp[1].dom.isPresent(i))) {
							foundSupport = true;
							break;
						}
					}
				if (!foundSupport) {
					nbModifications++;
					m[i][j] = m[i][j] = 0;
				}
			}
		if (nbModifications > 0) {
			mustComputeTarget = true;
			initialTargetGraph.computeNodesAtDistance1(); // keep it here
			if (neighbors1 != null)
				neighbors1.reconsiderTargetNodes(initialTargetGraph.nodesAtDistance1);
			if (neighbors2 != null)
				neighbors2.reconsiderTargetNodes(initialTargetGraph.computeNodesAtDistance2());
			if (neighbors1And2 != null)
				neighbors1And2.reconsiderTargetNodes(initialTargetGraph.computeNodesAtDistance1And2());
			Kit.log.info("nbRemovedEdges=" + nbModifications);
		} else
			mustComputeTarget = false;
		return nbModifications;
	}

	private boolean isMultisetDominated(long[] t1, long[] t2) {
		if (!useMultiset)
			return true;
		int d = t2.length - t1.length;
		for (int i = t1.length - 1; i >= 0; i--)
			if (t1[i] > t2[i + d])
				return false;
		return true;
	}

	private long[] copyAdjacenceAtRow(long[] src, long[] dst, int exceptValuePosition) {
		Kit.control(dst.length == src.length - (exceptValuePosition != -1 ? 1 : 0));
		if (exceptValuePosition != -1) {
			for (int cnt = 0, i = 0; i < src.length; i++)
				if (exceptValuePosition != i)
					dst[cnt++] = src[i];
		} else
			System.arraycopy(src, 0, dst, 0, src.length);
		return dst;
	}

	private long[][] copyAdjacence(long[][] src, long[][] dst) {
		Kit.control(dst.length == src.length);
		for (int i = 0; i < dst.length; i++)
			copyAdjacenceAtRow(src[i], dst[i], i);
		return dst;
	}

	private long[][] times(GraphSimpleUndirected initialGraph, long[][] m2) {
		long[][] adjacence = new long[initialGraph.nNodes][initialGraph.nNodes];
		long[][] m1 = initialGraph.adjacency;
		for (int i = 0; i < initialGraph.nNodes; i++)
			for (int j = 0; j <= i; j++) {
				int sum = 0;
				for (int k : initialGraph.nodesAtDistance1[i])
					// = 0; k < nbNodes; k++)
					sum += m1[i][k] * m2[k][j];
				adjacence[i][j] = adjacence[j][i] = sum;
			}
		return adjacence;
	}

	private int filter(long[][] patternAdjacence, long[][] targetAdjacence) {
		int nbValuesBefore = solver.pb.nValuesRemoved;
		if (neighbors1 != null)
			neighbors1.recordScores(patternAdjacence, targetAdjacence);
		if (neighbors2 != null)
			neighbors2.recordScores(patternAdjacence, targetAdjacence);
		if (neighbors1And2 != null)
			neighbors1And2.recordScores(patternAdjacence, targetAdjacence);
		if (useMultiset)
			for (long[] t : copyAdjacence(targetAdjacence, targetsMultiset))
				Kit.sort(t);
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			int num = x.num;
			if (useMultiset)
				Kit.sort(copyAdjacenceAtRow(patternAdjacence[num], patternMultiset, num));
			Domain dom = x.dom;
			int sizeBefore = dom.size();
			for (int idx = dom.first(); idx != -1; idx = dom.next(idx)) {
				if (patternAdjacence[num][num] > targetAdjacence[idx][idx] || (neighbors1 != null && !neighbors1.isNeighborDominated(num, idx))
				// || (neighbors2 != null && !neighbors2.isNeighborDominated(i, j))
				// || (neighbors1And2 != null && !neighbors1And2.isNeighborDominated(i, j))
						|| (useMultiset && !isMultisetDominated(patternMultiset, targetsMultiset[idx]))) {
					dom.removeElementary(idx);
					// Kit.prn("removal of " + var + " " + j);
				}
			}
			if (dom.size() == 0)
				return Integer.MAX_VALUE;
			if (sizeBefore > dom.size())
				queue.add(x);
		}
		return solver.pb.nValuesRemoved - nbValuesBefore;
	}

	// private int turn = 4;

	// return Boolean.FALSE when wipeout, Boolean.TRUE when overflow, null otherwise
	private Boolean filterFromAdjacences() {
		patternMatrices[0] = mustComputePattern || patternMatrices[0] == null ? Kit.cloneDeeply(initialPatternGraph.adjacency) : patternMatrices[0];
		targetMatrices[0] = mustComputeTarget || targetMatrices[0] == null ? Kit.cloneDeeply(initialTargetGraph.adjacency) : targetMatrices[0];

		for (int i = 0;; i++) {
			// if (i == turn) {
			// Kit.prn("i=" + (i + 1));
			// Kit.prn("patt" + i + "\n" + Kit.implode2D(storedPatternMatrices[i]));
			// Kit.prn("targ" + i + "\n" + Kit.implode2D(storedTargetMatrices[i]));
			// }
			int nbRemovals = 0;
			// if (i == turn)
			nbRemovals = filter(patternMatrices[i], targetMatrices[i]);

			if (nbRemovals > 0 || i < NB_MIN_TURNS) {
				if (trace)
					Kit.log.info("At " + i + " NbRems= " + nbRemovals + " sum=" + solver.pb.nValuesRemoved);
				if (nbRemovals == Integer.MAX_VALUE)
					return Boolean.FALSE;
			} else
				return null;
			// } else if (i > turn) return false;

			patternMatrices[i + 1] = mustComputePattern || patternMatrices[i + 1] == null ? times(initialPatternGraph, patternMatrices[i])
					: patternMatrices[i + 1];
			targetMatrices[i + 1] = mustComputeTarget || targetMatrices[i + 1] == null ? times(initialTargetGraph, targetMatrices[i]) : targetMatrices[i + 1];

			if (!Kit.withNoNegativeValues(patternMatrices[i + 1]) || !Kit.withNoNegativeValues(targetMatrices[i + 1])) {
				if (trace)
					Kit.log.info("stop due to overflow at " + i);
				// mustComputePattern = false;
				return Boolean.TRUE;
			}
		}

	}

	public PropagationIsomorphism(Solver solver) {
		super(solver);
		buildGraphs();
	}

	@Override
	public boolean runInitially() {
		Boolean consistent = null;
		while (consistent == null) {
			Boolean result = filterFromAdjacences();
			if (result == Boolean.FALSE) // Variable.getFirstWipeoutVariableIn(solver.problem.variables) != null)
				consistent = Boolean.FALSE;
			else if (!super.runInitially()) // AC
				consistent = Boolean.FALSE;
			else {
				int nbModifications = modifyAdjacence();
				if (result == null && nbModifications == 0)
					consistent = Boolean.TRUE;
			}
		}
		assert queue.size() == 0;
		mustComputeTarget = false;
		useMultiset = false;
		return consistent;
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		// if (!variable.domain.isModifiedAtCurrentDepth()) return true;
		if (!cp().propagating.strongOnlyAtPreprocessing) {
			Boolean result = filterFromAdjacences();
			if (result == Boolean.FALSE)
				return false;
			if (!super.runAfterAssignment(x)) // AC
				return false;
			return true;
		}
		return super.runAfterAssignment(x);
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		return super.runAfterRefutation(x);
	}

}

// private boolean test = true;// if (test) {
// Variable[] variables = solver.problem.variables;
// Constraint[] constraints = solver.problem.constraints;
// int allDiffPos = constraints.length - 1;
// Constraint allDiff = constraints[allDiffPos];
// for (Variable var1 : variables) {
// for (Variable var2 : variables) {
// if (!var1.isNeighbourOf(var2))
// solver.assign(var2, 0);
// }
// for (Constraint con : constraints) {
// con.ignored = !con.isInvolved(var1);
// }
// // solver.backtrack();
// }
// // Kit.prn(solver.problem.constraints[])
// }