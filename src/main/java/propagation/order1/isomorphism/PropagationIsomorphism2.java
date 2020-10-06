/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.order1.isomorphism;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import constraints.Constraint;
import constraints.CtrHard;
import propagation.order1.AC;
import search.Solver;
import utility.Kit;
import utility.Kit.IntWithLongArrayScoreReverse;
import utility.operations.GraphSimpleUndirected;
import variables.Variable;
import variables.domains.Domain;

public class PropagationIsomorphism2 extends AC {

	// private final int NB_MIN_TURNS = 3;

	private final int NB_MAX_STORED_MATRICES = 50;

	private GraphSimpleUndirected initialPatternGraph, initialTargetGraph;

	private long[][][] storedPatternMatrices, storedTargetMatrices;

	private boolean useNeighbors1 = true, useNeighbors2 = true, useNeighbors1And2 = true, useMultiset = false;

	private NeighborhoodReasoning neighbors1, neighbors2, neighbors1And2;

	private long[] patternMultiset;
	private long[][] targetsMultiset;

	private int[] first, last, fixed, nLasts, fixedPatternNeighbors;

	private boolean trace = true;

	private boolean mustCompute = true;

	private Domain[] domains;

	private boolean isDominated(long[] t1, long[] t2) {
		Kit.control(t1.length == t2.length); // TODO to change into assert
		for (int i = t1.length - 1; i >= 0; i--)
			if (t1[i] > t2[i])
				return false;
		return true;
	}

	private class NeighborhoodReasoning {
		private class Nodes {
			private int i;

			private IntWithLongArrayScoreReverse[] pairs;

			private Nodes(int i, int[] indices) {
				this.i = i;
				pairs = new IntWithLongArrayScoreReverse[indices.length];
				for (int j = 0; j < pairs.length; j++)
					pairs[j] = new IntWithLongArrayScoreReverse(indices[j]);
			}

			private void recordAndSort(int limit, long[][][] storedMatrices) {
				if (pairs.length == 0)
					return;
				if (pairs[0].score == null) {
					for (IntWithLongArrayScoreReverse pair : pairs)
						pair.score = new long[limit + 1];
				} else
					Kit.control(pairs[0].score.length == limit + 1);

				for (IntWithLongArrayScoreReverse pair : pairs) {
					int j = pair.index;
					for (int k = 0; k <= limit; k++)
						pair.score[k] = storedMatrices[k][i][j];
				}
				// Arrays.sort(pairs);
			}

			private int findDominanceSupportFor(IntWithLongArrayScoreReverse pair, int from, int to, boolean first) {
				if (first) {
					for (int i = from; i < to; i++)
						if (isDominated(pair.score, pairs[i].score) && fixed[i] == -1 && domains[pair.index].isPresent(pairs[i].index))
							return i;
				} else {
					for (int i = from; i > to; i--)
						if (isDominated(pair.score, pairs[i].score) && fixed[i] == -1 && domains[pair.index].isPresent(pairs[i].index))
							return i;
				}
				return -1;
			}
		}

		private Nodes[] patterns, targets;

		private int nFixedPatternNeighbors;

		private NeighborhoodReasoning(int[][] patternNeighbours, int[][] targetNeighbours) {
			Kit.control(patternNeighbours.length == initialPatternGraph.nNodes && targetNeighbours.length == initialTargetGraph.nNodes);
			patterns = new Nodes[patternNeighbours.length];
			for (int i = 0; i < patterns.length; i++)
				patterns[i] = new Nodes(i, patternNeighbours[i]);
			targets = new Nodes[targetNeighbours.length];
			for (int i = 0; i < targets.length; i++)
				targets[i] = new Nodes(i, targetNeighbours[i]);
			// Kit.prn(Kit.implode2D(patternNeighbours));
		}

		private void reconsiderTargetNodes(int[][] targetNeighbours) {
			for (int i = 0; i < targets.length; i++)
				targets[i] = new Nodes(i, targetNeighbours[i]);
		}

		private void recordScores(int limit) {
			for (int i = 0; i < patterns.length; i++)
				patterns[i].recordAndSort(limit, storedPatternMatrices);
			for (int i = 0; i < targets.length; i++)
				targets[i].recordAndSort(limit, storedTargetMatrices);
		}

		private boolean fix(int k, int v) {
			first[k] = last[k] = v;
			fixed[v] = k;
			fixedPatternNeighbors[nFixedPatternNeighbors++] = k;
			// Kit.prn("fix " + k + " " + patternNeighbors[k] + " " + last[k]); // + " " patternNeighbors[k] )
			return true;
		}

		private boolean isNeighborDominated(int i, int j) {
			IntWithLongArrayScoreReverse[] patternScores = patterns[i].pairs, targetScores = targets[j].pairs;
			int nPatternNeighbors = patterns[i].pairs.length, nbTargetNeighbors = targets[j].pairs.length;

			// Kit.prn("Test dominance " + i + " " +j + " NBPN=" + nbPatternNeighbors + " nbTN=" + nbTargetNeighbors) ;
			if (nPatternNeighbors > nbTargetNeighbors)
				return false;

			// for (int k = 0; k < nbPatternNeighbors; k++)
			// if (Kit.lexicographicComparatorLong.compare(patternScores[k].score, targetScores[k].score) > 0)
			// return false;
			Arrays.fill(fixed, 0, nbTargetNeighbors, -1);
			Arrays.fill(nLasts, 0, nbTargetNeighbors, 0);
			nFixedPatternNeighbors = 0;
			for (int k = 0; k < nPatternNeighbors; k++) {
				first[k] = targets[j].findDominanceSupportFor(patternScores[k], 0, nbTargetNeighbors, true);
				if (first[k] == -1)
					return false;
				last[k] = targets[j].findDominanceSupportFor(patternScores[k], nbTargetNeighbors - 1, first[k], false);
				if (last[k] == -1) {
					fix(k, first[k]);
				}
				nLasts[last[k]]++;
			}
			while (true) {
				boolean newFixed = false;
				for (int k = 0; k < nPatternNeighbors; k++) {
					if (first[k] != last[k]) {
						int fixedLast = fixed[last[k]];
						if (fixed[first[k]] != -1) {
							first[k] = targets[j].findDominanceSupportFor(patternScores[k], first[k] + 1, last[k], true);
							if (first[k] == -1) {
								if (fixedLast != -1)
									return false;
								newFixed = fix(k, last[k]);
							}
						}
						if (fixedLast != -1) {
							nLasts[last[k]]--;
							last[k] = targets[j].findDominanceSupportFor(patternScores[k], last[k] - 1, first[k], false);
							if (last[k] == -1) {
								newFixed = fix(k, first[k]);
							}
							nLasts[last[k]]++;
						}
					}
				}
				if (!newFixed)
					break;
			}
			int sum = 0;
			for (int k = 0; k < nPatternNeighbors; k++) {
				sum += nLasts[k];
				if (sum > k + 1)
					return false;
			}
			boolean test = true;
			// if (nFixedPatternNeighbors > 1)
			// Kit.prn("nFixed=" + nFixedPatternNeighbors);
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
		storedPatternMatrices = new long[NB_MAX_STORED_MATRICES][][];
		storedTargetMatrices = new long[NB_MAX_STORED_MATRICES][][];
		first = new int[initialPatternGraph.nNodes];
		last = new int[initialPatternGraph.nNodes];
		fixed = new int[initialTargetGraph.nNodes];
		nLasts = new int[initialTargetGraph.nNodes];
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
			mustCompute = true;
			initialTargetGraph.computeNodesAtDistance1(); // keep it here
			if (neighbors1 != null)
				neighbors1.reconsiderTargetNodes(initialTargetGraph.nodesAtDistance1);
			if (neighbors2 != null)
				neighbors2.reconsiderTargetNodes(initialTargetGraph.computeNodesAtDistance2());
			if (neighbors1And2 != null)
				neighbors1And2.reconsiderTargetNodes(initialTargetGraph.computeNodesAtDistance1And2());
			Kit.log.info("nbRemovedEdges=" + nbModifications);
		}
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

	@SuppressWarnings("unused")
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

	private boolean isPivotDominated(int i, int j, int limit) {
		for (int k = 0; k <= limit; k++)
			if (storedPatternMatrices[k][i][i] > storedTargetMatrices[k][j][j])
				return false;
		return true;

	}

	private int filter(int limit) {
		int nbValuesBefore = solver.pb.nValuesRemoved;
		if (neighbors1 != null)
			neighbors1.recordScores(limit);
		if (neighbors2 != null)
			neighbors2.recordScores(limit);
		if (neighbors1And2 != null)
			neighbors1And2.recordScores(limit);
		// if (useMultiset) for (long[] t : copyAdjacence(targetAdjacence, targetsMultiset)) Kit.sort(t);
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			int num = x.num;
			// if (useMultiset) Kit.sort(copyAdjacenceAtRow(patternAdjacence[i], patternMultiset, i));
			Domain dom = x.dom;
			int sizeBefore = dom.size();
			for (int idx = dom.first(); idx != -1; idx = dom.next(idx)) {
				if (!isPivotDominated(num, idx, limit) || (neighbors1 != null && !neighbors1.isNeighborDominated(num, idx))
						|| (neighbors2 != null && !neighbors2.isNeighborDominated(num, idx))
						|| (neighbors1And2 != null && !neighbors1And2.isNeighborDominated(num, idx))
						|| (useMultiset && !isMultisetDominated(patternMultiset, targetsMultiset[idx]))) {
					dom.removeElementary(idx);
					// Kit.prn("removal of " + variables[i] + " " + j);
				}
			}
			if (sizeBefore > dom.size())
				queue.add(x);
		}
		return solver.pb.nValuesRemoved - nbValuesBefore;
	}

	private boolean filterFromAdjacences() {
		storedPatternMatrices[0] = mustCompute || storedPatternMatrices[0] == null ? Kit.cloneDeeply(initialPatternGraph.adjacency) : storedPatternMatrices[0];
		storedTargetMatrices[0] = mustCompute || storedTargetMatrices[0] == null ? Kit.cloneDeeply(initialTargetGraph.adjacency) : storedTargetMatrices[0];

		int i = 0;
		for (;; i++) {
			storedPatternMatrices[i + 1] = mustCompute || storedPatternMatrices[i + 1] == null ? times(initialPatternGraph, storedPatternMatrices[i])
					: storedPatternMatrices[i + 1];
			storedTargetMatrices[i + 1] = mustCompute || storedTargetMatrices[i + 1] == null ? times(initialTargetGraph, storedTargetMatrices[i])
					: storedTargetMatrices[i + 1];
			if (!Kit.withNoNegativeValues(storedPatternMatrices[i + 1]) || !Kit.withNoNegativeValues(storedTargetMatrices[i + 1])) {
				break;
			}
		}
		int nbRemovals = filter(i);
		if (nbRemovals > 0) {
			if (trace)
				Kit.log.info("At " + i + " NbRems= " + nbRemovals + " sum=" + solver.pb.nValuesRemoved);
		}
		return nbRemovals > 0;
	}

	public PropagationIsomorphism2(Solver solver) {
		super(solver);
		buildGraphs();
	}

	@Override
	public boolean runInitially() {
		Boolean consistent = null;
		while (consistent == null) {
			boolean removals = filterFromAdjacences();
			if (Variable.firstWipeoutVariableIn(solver.pb.variables) != null)
				consistent = Boolean.FALSE;
			else if (!super.runInitially()) // AC
				consistent = Boolean.FALSE;
			else {
				int nbModifications = modifyAdjacence();
				if (!removals && nbModifications == 0)
					consistent = Boolean.TRUE;
			}
		}
		assert queue.size() == 0;
		mustCompute = false;
		useMultiset = false;
		return consistent;
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		// if (!variable.domain.isModifiedAtCurrentDepth()) return true;

		// boolean overflow = filterFromAdjacences();
		// if (Variable.getFirstWipeoutVariableIn(solver.problem.variables) != null)
		// return false;
		// if (!super.enforceAfterAssignmentOf(variable)) // AC
		// return false;
		// return true;

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