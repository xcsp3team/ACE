/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import static java.util.stream.Collectors.joining;
import static utility.Kit.control;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.global.AllDifferent.AllDifferentComplete;
import interfaces.Observers.ObserverOnConstruction;
import problem.Problem;
import sets.SetSparse;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * The object used to compute a maximal matching, and to delete inconsistent values <br/>
 * TODO : the algorithm is poorly incremental, and besides is recursive (how to avoid recursion?)
 * 
 * @author Vincent Perradin (refactoring by Christophe Lecoutre)
 */
public abstract class Matcher implements ObserverOnConstruction {

	@Override
	public void afterProblemConstruction(int n) {
		this.unfixedVars = new SetSparseReversible(arity, n + 1);
		if (this instanceof MatcherAllDifferent)
			this.fixedVars = new SetSparseReversible(arity, n + 1, false);
	}

	public void restoreAtDepthBefore(int depth) {
		unfixedVars.restoreLimitAtLevel(depth);
		if (fixedVars != null)
			fixedVars.restoreLimitAtLevel(depth);
	}

	/**
	 * The problem to which this object is (indirectly) attached
	 */
	protected final Problem problem;

	/**
	 * The scope of the constraint to which this object is attached
	 */
	protected final Variable[] scp;

	protected final int arity;

	protected final int minValue, maxValue;

	protected final int intervalSize;

	protected final int T; // special node

	/**
	 * current time (for stamping)
	 */
	protected int time;

	/**
	 * variables that have no singleton domains
	 */
	protected SetSparseReversible unfixedVars;

	protected SetSparseReversible fixedVars;

	/**
	 * queue of currently unmatched variables
	 */
	protected final SetSparse unmatchedVars;

	/**
	 * varToVal[x] gives the value assigned to x in the current matching, or -1
	 */
	protected final int[] varToVal;

	/**
	 * visitTime[n] is the time of the last visit (DFS) to node n (variable or value or T)
	 */
	protected final int[] visitTime;

	/**
	 * number of visited nodes in the current DFS
	 */
	protected int nVisitedNodes;

	/**
	 * numDFS[n] is the number (order) of node n when reached/discovered during DFS
	 */
	private final int[] numDFS;

	/**
	 * lowLink[n] is the minimum number of all nodes reachable from node n by following edges used by the current DFS
	 */
	protected final int[] lowLink;

	/**
	 * stack used to compute strongly connected components in the current DFS
	 */
	private final SetSparse stackTarjan;

	/**
	 * neighborsOfValues[u] contains all neighbors (nodes) of node u. We have possibly arity + 1 (for node T) such
	 * nodes.
	 */
	protected SetSparse[] neighborsOfValues;

	/**
	 * set containing all neighbors of vertex T
	 */
	protected SetSparse neighborsOfT;

	/**
	 * Boolean used when computing strongly connected components in the current DFS
	 */
	protected boolean splitSCC;

	/**
	 * current strongly connected component
	 */
	private SetSparse currValsSCC;

	protected final SetSparse currVarsSCC;

	/**
	 * queue used to perform BFS
	 */
	protected SetSparse queueBFS;

	/**
	 * predBFS[x] is the predecessor of variable x in the current BFS
	 */
	protected int[] predBFS;

	public Matcher(Constraint c) {
		this.problem = c.problem;
		this.scp = c.scp;
		this.arity = c.scp.length;

		this.minValue = Stream.of(scp).mapToInt(x -> x.dom.firstValue()).min().getAsInt();
		this.maxValue = Stream.of(scp).mapToInt(x -> x.dom.lastValue()).max().getAsInt();
		this.intervalSize = maxValue - minValue + 1;
		this.T = arity + intervalSize;

		this.unmatchedVars = new SetSparse(arity);
		this.varToVal = Kit.repeat(-1, arity);
		this.currVarsSCC = new SetSparse(arity);

		this.neighborsOfValues = IntStream.range(0, intervalSize).mapToObj(i -> new SetSparse(arity + 1)).toArray(SetSparse[]::new);
		this.neighborsOfT = new SetSparse(intervalSize);
		this.currValsSCC = new SetSparse(intervalSize);

		int nNodes = arity + intervalSize + 1;
		this.visitTime = Kit.repeat(-1, nNodes);
		this.stackTarjan = new SetSparse(nNodes);
		this.numDFS = new int[nNodes];
		this.lowLink = new int[nNodes];

		c.problem.head.observersConstruction.add(this);

		// TODO use classical sets (not sparse sets or arrays) if big gap between
		// minValue and maxValue AND number of values is a lot smaller than maxValue-minValue
	}

	protected abstract boolean findMaximumMatching();

	protected abstract void computeNeighbors();

	/**
	 * Computes Tarjan algorithm and prunes some values from the domains. Nodes are given a number as follows: a) i for
	 * the ith variable of the scope, b) arity+v for a value v between minValue and maxValue, c) arity+intervalSize for
	 * node T
	 * 
	 * @param node
	 *            : Starting vertex for the search
	 */
	protected final void tarjanRemoveValues(int node) {
		assert visitTime[node] < time;
		visitTime[node] = time;
		numDFS[node] = lowLink[node] = ++nVisitedNodes;
		stackTarjan.add(node);

		if (node < arity) { // node for a variable
			int adjacentNode = arity + varToVal[node];
			if (visitTime[adjacentNode] != time) { // This code is repeated 3 times to save stacking (recursive calls)
				tarjanRemoveValues(adjacentNode);
				lowLink[node] = Math.min(lowLink[node], lowLink[adjacentNode]);
			} else if (stackTarjan.contains(adjacentNode))
				lowLink[node] = Math.min(lowLink[node], numDFS[adjacentNode]);
		} else if (node < T) { // node for a value
			SetSparse neighbors = neighborsOfValues[node - arity];
			for (int i = 0; i <= neighbors.limit; i++) {
				int adjacentNode = neighbors.dense[i] == arity ? T : neighbors.dense[i];
				if (visitTime[adjacentNode] != time) {
					tarjanRemoveValues(adjacentNode);
					lowLink[node] = Math.min(lowLink[node], lowLink[adjacentNode]);
				} else if (stackTarjan.contains(adjacentNode))
					lowLink[node] = Math.min(lowLink[node], numDFS[adjacentNode]);
			}
		} else {
			assert node == T; // node for T
			for (int i = 0; i <= neighborsOfT.limit; i++) {
				int adjacentNode = arity + neighborsOfT.dense[i];
				if (visitTime[adjacentNode] != time) {
					tarjanRemoveValues(adjacentNode);
					lowLink[node] = Math.min(lowLink[node], lowLink[adjacentNode]);
				} else if (stackTarjan.contains(adjacentNode))
					lowLink[node] = Math.min(lowLink[node], numDFS[adjacentNode]);
			}
		}
		if (lowLink[node] == numDFS[node]) { // if node is the root of a SCC
			splitSCC = splitSCC || lowLink[node] > 1 || nVisitedNodes < visitTime.length;
			if (splitSCC) {
				// if (node == T) {
				// int nodeSCC = -1;
				// while (nodeSCC != node)
				// nodeSCC = stackTarjan.pop();
				// return;
				// }

				currVarsSCC.resetTo(unfixedVars);
				currValsSCC.clear();
				int nodeSCC = -1;
				while (nodeSCC != node) {
					nodeSCC = stackTarjan.pop();
					if (nodeSCC < arity)
						currVarsSCC.remove(nodeSCC);
					else if (nodeSCC < T)
						currValsSCC.add(nodeSCC - arity);
				}
				// System.out.println(" hhh " + node + " " + currVarsSCC.size() + " " + currValsSCC.size());
				// System.out.println("fff " + currVarsSCC.size() + " " + currValsSCC.size());
				if (currVarsSCC.size() > 0)
					for (int i = 0; i <= currValsSCC.limit; i++) {
						int v = currValsSCC.dense[i];
						SetSparse neighbors = neighborsOfValues[v];
						if (neighbors.size() < currVarsSCC.size()) {
							int w = domainValueOf(v);
							for (int j = 0; j <= neighbors.limit; j++) {
								int x = neighbors.dense[j];
								if (x < arity && currVarsSCC.contains(x) && varToVal[x] != v)
									scp[x].dom.removeValue(w);
							}
						} else
							for (int j = 0; j <= currVarsSCC.limit; j++) {
								int x = currVarsSCC.dense[j];
								int a = scp[x].dom.toIdxIfPresent(domainValueOf(v));
								if (a >= 0 && varToVal[x] != v)
									scp[x].dom.remove(a);
							}
					}
			}
		}

	}

	/**
	 * Finds the strongly connected components of the flow graph as defined in Ian P. Gent, Ian Miguel, and Peter
	 * Nightingale, The AllDifferent Constraint: An Empirical Survey, and prunes the domains to reach (G)AC
	 */
	public final void removeInconsistentValues() {
		time++;
		computeNeighbors();
		stackTarjan.clear();
		splitSCC = false;
		nVisitedNodes = 0;
		for (int x = 0; x < arity; x++) {
			if (fixedVars != null && fixedVars.contains(x))
				continue;
			if (visitTime[x] < time)
				tarjanRemoveValues(x);
		}
	}

	/**
	 * @param normalizedValue
	 *            : index between 0 and (maxDomainValue - minDomainValue). Domain values used in this class are
	 *            normalized to use Sparse containers
	 * 
	 * @return domain value corresponding to the normalized value in parameter
	 */
	protected int domainValueOf(int normalizedValue) {
		return normalizedValue + minValue;
	}

	/**
	 * @param domainValue
	 *            : any domain value
	 * 
	 * @return normalized value between 0 and (maxDomainValue - minDomainValue), corresponding to the domain value in
	 *         parameter. Domain values used in this class are normalized to use Sparse containers
	 */
	protected int normalizedValueOf(int domainValue) {
		return domainValue - minValue;
	}

	/**********************************************************************************************
	 * MatcherAllDifferent
	 *********************************************************************************************/

	/**
	 * Class used to perform AC filtering for AllDifferent
	 */
	public static class MatcherAllDifferent extends Matcher {

		/**
		 * The variable each value is assigned to in the current matching
		 */
		private final int[] valToVar;

		public MatcherAllDifferent(AllDifferentComplete c) {
			super(c);
			this.queueBFS = new SetSparse(arity);
			this.predBFS = Kit.repeat(-1, arity);
			this.valToVar = Kit.repeat(-1, intervalSize);
		}

		/**
		 * Finds a matching for the unmatched parameter variable while keeping the matched variables (may change the
		 * matched values though).
		 * 
		 * @param x
		 *            : An unmatched variable
		 * @return true if a matching has been found for the variable, false otherwise (constraint unsatisfiable)
		 */
		private boolean findMatchingFor(int x) {
			time++;
			predBFS[x] = -1;
			queueBFS.resetTo(x);
			while (!queueBFS.isEmpty()) {
				int y = queueBFS.shift();
				Domain dom = scp[y].dom;
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					int v = normalizedValueOf(dom.toVal(a));
					int z = valToVar[v];
					assert z == -1 || varToVal[z] == v;
					if (z == -1) { // we have found a free value, so we are good
						while (predBFS[y] != -1) {
							int w = varToVal[y];
							varToVal[y] = v;
							valToVar[v] = y;
							v = w;
							y = predBFS[y];
						}
						varToVal[y] = v;
						valToVar[v] = y;
						return true;
					} else if (visitTime[z] < time) {
						visitTime[z] = time;
						predBFS[z] = y;
						queueBFS.add(z);
					}
				}
			}
			return false;
		}

		/**
		 * Finds a matching for all the unmatched variables while keeping the matched variables (may change the matched
		 * values though).
		 * 
		 * @return true if a matching has been found, false otherwise (constraint unsatisfiable)
		 */
		@Override
		public boolean findMaximumMatching() {
			unmatchedVars.clear();
			int depth = problem.solver.depth();
			for (int x = 0; x < arity; x++) {
				int v = varToVal[x];
				if (v == -1)
					unmatchedVars.add(x);
				else {
					assert valToVar[v] == x;
					if (!scp[x].dom.containsValue(domainValueOf(v))) {
						varToVal[x] = valToVar[v] = -1;
						unmatchedVars.add(x);
					}
					if (scp[x].dom.size() == 1 && unfixedVars.contains(x))
						unfixedVars.remove(x, depth);
				}
			}
			while (!unmatchedVars.isEmpty())
				if (!findMatchingFor(unmatchedVars.pop()))
					return false;
			return true;
		}

		/**
		 * Computes the neighbors of each value vertex and those of vertex T in the flow graph
		 */
		@Override
		protected void computeNeighbors() {
			int depth = problem.solver.depth();
			for (SetSparse set : neighborsOfValues)
				set.clear();
			neighborsOfT.clear();
			for (int x = 0; x < arity; x++) {
				if (fixedVars.contains(x))
					continue;
				Domain dom = scp[x].dom;
				if (dom.size() == 1) { // we discard trivial SCCs (variable assignments) after treating them
					int v = dom.singleValue();
					for (int j = unfixedVars.limit; j >= 0; j--) {
						int y = unfixedVars.dense[j];
						if (y != x) {
							int a = scp[y].dom.toIdxIfPresent(v);
							if (a >= 0)
								scp[y].dom.remove(a); // no possible inconsistency
						}
					}
					fixedVars.add(x, depth);
					continue;
				}
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					int v = normalizedValueOf(dom.toVal(a));
					neighborsOfValues[v].add(x);
					if (valToVar[v] == x)
						neighborsOfValues[v].add(arity); // E3
					else {
						neighborsOfValues[v].add(x); // E2
						if (valToVar[v] == -1) // unmatched values
							neighborsOfT.add(v); // E4
					}
				}
			}

		}

		@Override
		public String toString() {
			return "varToVal: " + Kit.join(varToVal) + "\nvalToVar: " + Kit.join(valToVar);
		}
	}

	/**********************************************************************************************
	 * MatcherCardinality
	 *********************************************************************************************/

	/**
	 * Class used to perform AC filtering for Cardinality
	 */
	public static class MatcherCardinality extends Matcher {

		/**
		 * Variables the values are matched to. In a GCC, a value can be matched to several variables.
		 */
		// private SetSparseReversible[] valToVars;
		private SetSparse[] valToVars;

		/**
		 * Constrained values
		 */
		private int[] keys;

		/**
		 * Normalized version of the minOccurrences array, for quick data access (but uses more space).
		 */
		private int[] minOccs;

		/**
		 * Normalized version of the maxOccurrences array, for quick data access (but uses more space).
		 */
		private int[] maxOccs;

		/**
		 * Set of the variables each value can be assigned to (the value is in these variables' initial domains).
		 */
		private final SetSparse[] possibleVars;

		/**
		 * Predecessor value of values in the DFS
		 */
		private int[] predValue;

		/**
		 * @param c
		 *            : Global cardinality constraint the algorithm will filter.
		 * @param scp
		 *            : Initial scope of the constraint.
		 * @param keys
		 *            : Constrained values.
		 * @param minOccs
		 *            : Number of times each value should be assigned at least.
		 * @param maxOccs
		 *            : Number of times each value should be assigned at most.
		 */
		public MatcherCardinality(Cardinality c, int[] keys, int[] minOccs, int[] maxOccs) {
			super(c);
			this.keys = keys;
			control(this.minValue <= IntStream.of(keys).min().getAsInt());
			control(this.maxValue >= IntStream.of(keys).max().getAsInt());

			// this.minValue = Math.min(this.minValue, IntStream.of(keys).min().getAsInt());
			// this.maxValue = Math.max(this.maxValue, IntStream.of(keys).max().getAsInt());
			// this.intervalSize = maxValue - minValue + 1;
			// this.T = arity + intervalSize;

			this.queueBFS = new SetSparse(Math.max(arity, intervalSize));
			this.predBFS = Kit.repeat(-1, Math.max(arity, intervalSize));

			this.predValue = Kit.repeat(-1, intervalSize);

			this.minOccs = new int[intervalSize];
			this.maxOccs = Kit.repeat(Integer.MAX_VALUE, intervalSize);
			for (int i = 0; i < keys.length; i++) {
				this.minOccs[normalizedValueOf(keys[i])] = minOccs[i];
				this.maxOccs[normalizedValueOf(keys[i])] = maxOccs[i];
			}

			this.possibleVars = new SetSparse[intervalSize];
			for (int u = 0; u < intervalSize; u++) {
				possibleVars[u] = new SetSparse(arity);
				for (int x = 0; x < arity; x++)
					if (scp[x].dom.containsValue(domainValueOf(u)))
						possibleVars[u].add(x);
			}

			this.valToVars = IntStream.range(0, intervalSize).mapToObj(i -> new SetSparse(arity, false)).toArray(SetSparse[]::new);
		}

		private void handleAugmentingPath(int x, int v) {
			while (predBFS[v] != -1) {
				int y = predBFS[v];
				varToVal[x] = v;
				valToVars[v].add(x);
				valToVars[v].remove(y);
				x = y;
				v = predValue[v];
			}
			varToVal[x] = v;
			valToVars[v].add(x);
		}

		private boolean findMatchingForValue(int u) {
			time++;
			queueBFS.resetTo(u);
			predBFS[u] = -1;
			visitTime[u] = time;
			while (!queueBFS.isEmpty()) {
				int v = queueBFS.shift();
				for (int i = 0; i <= possibleVars[v].limit; i++) {
					int x = possibleVars[v].dense[i];
					Domain dom = scp[x].dom;
					if (dom.containsValue(domainValueOf(v))) {
						int w = varToVal[x];
						if (w == -1) {
							handleAugmentingPath(x, v);
							return true;
						} else if (w != v) {
							if (valToVars[w].size() > minOccs[w] && varToVal[x] == w) {
								valToVars[w].remove(x); // IfPresent(x);
								handleAugmentingPath(x, v);
								return true;
							} else if (visitTime[w] < time) {
								visitTime[w] = time;
								queueBFS.add(w);
								predBFS[w] = x;
								predValue[w] = v;
							}
						}
					}
				}
			}
			return false;
		}

		private boolean findMatchingForVariable(int x) {
			time++;
			queueBFS.resetTo(x);
			predBFS[x] = -1;
			visitTime[x] = time;
			while (!queueBFS.isEmpty()) {
				int y = queueBFS.shift();
				Domain dom = scp[y].dom;
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					int u = normalizedValueOf(dom.toVal(a));
					if (valToVars[u].size() < maxOccs[u]) {
						while (predBFS[y] != -1) {
							int v = varToVal[y]; // previous value
							varToVal[y] = u;
							valToVars[u].add(y);
							valToVars[v].remove(y);
							y = predBFS[y];
							u = v;
						}
						varToVal[y] = u;
						valToVars[u].add(y);
						return true;
					}
					for (int i = 0; i < valToVars[u].size(); i++) {
						int z = valToVars[u].dense[i];
						assert (varToVal[z] == u);
						if (visitTime[z] < time) {
							visitTime[z] = time;
							predBFS[z] = y;
							queueBFS.add(z);
						}
					}
				}
			}
			return false;
		}

		@Override
		public boolean findMaximumMatching() {
			// Make sure each variable is not matched with a value that is not in its domain anymore
			for (int x = 0; x < arity; x++) {
				Domain dom = scp[x].dom;
				int u = varToVal[x];
				if (u == -1 || !dom.containsValue(domainValueOf(u))) {
					if (dom.size() == 1) {
						int v = normalizedValueOf(dom.firstValue());
						if (u != -1)
							valToVars[u].remove(x);
						if (maxOccs[v] == valToVars[v].size()) {
							varToVal[x] = -1;
						} else {
							varToVal[x] = v;
							valToVars[v].add(x);
						}
					} else if (u != -1) {
						valToVars[u].remove(x);
						varToVal[x] = -1;
					}
				}
			}
			// Generate a feasible flow (part of the matching)
			for (int i = 0; i < keys.length; i++) {
				int u = normalizedValueOf(keys[i]);
				while (valToVars[u].size() < minOccs[u])
					if (!findMatchingForValue(u))
						return false;
			}
			unmatchedVars.clear();
			for (int x = 0; x < arity; x++) {
				if (varToVal[x] == -1)
					unmatchedVars.add(x);
				else if (scp[x].dom.size() == 1 && unfixedVars.contains(x))
					unfixedVars.remove(x, problem.solver.depth());
			}
			while (!unmatchedVars.isEmpty())
				if (!findMatchingForVariable(unmatchedVars.pop()))
					return false;
			return true;
		}

		@Override
		protected void computeNeighbors() {
			for (SetSparse set : neighborsOfValues)
				set.clear();
			for (int u = 0; u < intervalSize; u++) {
				if (valToVars[u].size() < maxOccs[u])
					neighborsOfT.add(u);
				else
					neighborsOfT.remove(u);
				if (valToVars[u].size() > minOccs[u])
					neighborsOfValues[u].add(arity);
				else
					neighborsOfValues[u].remove(arity);
				for (int i = 0; i <= possibleVars[u].limit; i++) {
					int x = possibleVars[u].dense[i];
					if (scp[x].dom.containsValue(domainValueOf(u)) && varToVal[x] != u)
						neighborsOfValues[u].add(x);
					else
						neighborsOfValues[u].remove(x);
				}
			}
		}

		private void checkMatchingConsistency() {
			control(IntStream.range(0, intervalSize)
					.allMatch(u -> IntStream.range(0, valToVars[u].size()).allMatch(i -> varToVal[valToVars[u].dense[i]] == u)));
			control(IntStream.range(0, arity).allMatch(x -> varToVal[x] == -1 || valToVars[varToVal[x]].contains(x)));
		}

		@SuppressWarnings("unused")
		private void checkMatchingValidity() {
			control(IntStream.range(0, arity).allMatch(x -> varToVal[x] != -1 && scp[x].dom.containsValue(domainValueOf(varToVal[x]))));
			control(IntStream.range(0, intervalSize).allMatch(u -> minOccs[u] <= valToVars[u].size() && valToVars[u].size() <= maxOccs[u]));
			checkMatchingConsistency();
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("varToVal : " + IntStream.of(varToVal).mapToObj(u -> domainValueOf(u) + " ").collect(joining()));
			sb.append("\nvalue2Variables :\n");
			for (int u = 0; u < intervalSize; u++) {
				sb.append("Value " + domainValueOf(u) + " : ");
				for (int i = 0; i <= valToVars[u].limit; i++)
					sb.append(valToVars[u].dense[i] + " ");
				sb.append("\n");
			}
			sb.append("predVariable : " + Kit.join(predBFS) + "\n");
			return sb.toString();
		}
	}

}
