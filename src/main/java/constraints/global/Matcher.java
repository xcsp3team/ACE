package constraints.global;

import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.global.AllDifferent.AllDifferentComplete;
import constraints.global.Cardinality.CardinalityConstant;
import interfaces.Observers.ObserverOnConstruction;
import sets.SetSparse;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public abstract class Matcher implements ObserverOnConstruction {

	public void restoreAtDepthBefore(int depth) {
		unfixedVars.restoreLimitAtLevel(depth);
	}

	protected final Constraint ctr;

	protected final Variable[] scp;

	protected final int arity;

	protected int minValue, maxValue;

	protected int intervalSize;

	/**
	 * current time (for stamping)
	 */
	protected int time;

	/**
	 * variables that have no singleton domains
	 */
	protected SetSparseReversible unfixedVars;

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
	protected int[] visitTime;

	/**
	 * number of visited nodes in the current DFS
	 */
	protected int nVisitedNodes;

	/**
	 * numDFS[n] is the number (order) of node n when reached/discovered during DFS
	 */
	protected int[] numDFS;

	/**
	 * lowLink[n] is the minimum number of all nodes reachable from node n by following edges used by the current DFS
	 */
	protected int[] lowLink;

	/**
	 * stack used to compute strongly connected components in the current DFS
	 */
	protected SetSparse stackTarjan;

	/**
	 * neighborsOfValues[u] contains all neighbors (nodes) of node u. We have possibly arity + 1 (for node T) such nodes.
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
	protected SetSparse currValsSCC;

	protected SetSparse currVarsSCC;

	/**
	 * queue used to perform BFS
	 */
	protected SetSparse queueBFS;

	/**
	 * predBFS[x] is the predecessor of variable x in the current BFS
	 */
	protected int[] predBFS;

	public Matcher(Constraint ctr, Variable[] scp) {
		this.ctr = ctr;
		this.scp = scp;
		this.arity = scp.length;

		this.unmatchedVars = new SetSparse(arity);
		this.varToVal = Kit.repeat(-1, arity);
		this.currVarsSCC = new SetSparse(arity);

		this.minValue = Stream.of(scp).mapToInt(x -> x.dom.firstValue()).min().getAsInt();
		this.maxValue = Stream.of(scp).mapToInt(x -> x.dom.lastValue()).max().getAsInt();
		this.intervalSize = maxValue - minValue + 1;

		ctr.problem.head.observersConstruction.add(this);

		// TODO use classical sets (not sparse sets or arrays) if big gap between
		// minValue and maxValue AND number of values is a lot smaller than maxValue-minValue
	}

	@Override
	public void afterProblemConstruction() {
		unfixedVars = new SetSparseReversible(arity, ctr.problem.variables.length + 1);

		neighborsOfValues = IntStream.range(0, intervalSize).mapToObj(i -> new SetSparse(arity + 1)).toArray(SetSparse[]::new);
		neighborsOfT = new SetSparse(intervalSize);
		currValsSCC = new SetSparse(intervalSize);

		int nNodes = arity + intervalSize + 1;
		visitTime = Kit.repeat(-1, nNodes);
		stackTarjan = new SetSparse(nNodes);
		numDFS = new int[nNodes];
		lowLink = new int[nNodes];

	}

	protected abstract boolean findMaximumMatching();

	protected abstract void computeNeighbors();

	private void update(int adjacentNode, int node) {
		if (visitTime[adjacentNode] == time) {
			if (stackTarjan.contains(adjacentNode) && numDFS[adjacentNode] < lowLink[node])
				lowLink[node] = numDFS[adjacentNode];
		} else {
			tarjanRemoveValues(adjacentNode);
			if (lowLink[adjacentNode] < lowLink[node])
				lowLink[node] = lowLink[adjacentNode];
		}
	}

	/**
	 * Computes Tarjan algorithm and prunes some values from the domains. Nodes are given a number as follows: a) i for the ith variable of the scope, b)
	 * arity+v for a value v between minValue and maxValue, c) arity+intervalSize for node T
	 * 
	 * @param node
	 *            : Starting vertex for the search
	 */
	protected final void tarjanRemoveValues(int node) {
		// System.out.println("TRV = " + node);
		assert visitTime[node] < time;
		visitTime[node] = time;
		numDFS[node] = lowLink[node] = ++nVisitedNodes;
		stackTarjan.add(node);

		if (node < arity) {// node for a variable {
			update(arity + varToVal[node], node);
		} else if (node < arity + intervalSize) { // node for a value
			SetSparse neighbors = neighborsOfValues[node - arity];
			for (int i = 0; i <= neighbors.limit; i++)
				update(neighbors.dense[i] == arity ? arity + intervalSize : neighbors.dense[i], node);
		} else {
			assert node == arity + intervalSize; // node for T
			for (int i = 0; i <= neighborsOfT.limit; i++)
				update(arity + neighborsOfT.dense[i], node);
		}
		if (lowLink[node] == numDFS[node]) {
			splitSCC = splitSCC || (lowLink[node] > 1 || nVisitedNodes < visitTime.length);
			if (splitSCC) {
				currVarsSCC.clear();
				// for (int j = 0; j <= ctr.futvars.limit; j++) { // j >= 0; j--) {
				// int x = ctr.futvars.dense[j];
				// if (scp[x].dom.size() > 1)
				// currVarsSCC.add(x);
				// }

				for (int j = 0; j <= unfixedVars.limit; j++)
					currVarsSCC.add(unfixedVars.dense[j]);
				currValsSCC.clear();
				int nodeSCC = -1;
				while (nodeSCC != node) {
					nodeSCC = stackTarjan.pop();
					if (nodeSCC < arity)
						currVarsSCC.remove(nodeSCC);
					else if (arity <= nodeSCC && nodeSCC < arity + intervalSize)
						currValsSCC.add(nodeSCC - arity);
				}
				// System.out.println(this + " valsSize=" + currValsSCC.size());
				// System.out.println("Size= " + currVarsSCC.size() + " vs " + unfixedVars.size());
				if (currVarsSCC.size() > 0)
					for (int i = 0; i <= currValsSCC.limit; i++) {
						int u = currValsSCC.dense[i];
						for (int j = 0; j <= currVarsSCC.limit; j++) {
							int x = currVarsSCC.dense[j];
							int a = scp[x].dom.toIdxIfPresent(domainValueOf(u));
							if (a >= 0 && varToVal[x] != u)
								scp[x].dom.remove(a);
						}

						// for (int j = ctr.futvars.limit; j >= 0; j--) {
						// int x = ctr.futvars.dense[j];
						// int a = scp[x].dom.toPresentIdx(domainValueOf(u));
						// if (a >= 0 && !currSCC.isPresent(x) && varToVal[x] != u)
						// scp[x].dom.remove(a);
						// }
						// int nb = ctr.pb.nValuesRemoved;
						// for (int j = 0; j <= unfixedVars.limit; j++) {
						// int x = unfixedVars.dense[j];
						// int a = scp[x].dom.toPresentIdx(domainValueOf(u));
						// if (a >= 0 && !currSCC.isPresent(x) && varToVal[x] != u)
						// scp[x].dom.remove(a);
						// }
						// System.out.println(ctr + " while removing " + domainValueOf(u) + " DIff=" + (ctr.pb.nValuesRemoved - nb) + " " +
						// currSCC.size());
					}
				// }
			}
		}
	}

	/**
	 * Finds the strongly connected components of the flow graph as defined in Ian P. Gent, Ian Miguel, and Peter Nightingale, The AllDifferent Constraint: An
	 * Empirical Survey, and prunes the domains to reach GAC
	 */
	public final void removeInconsistentValues() {
		time++;
		computeNeighbors();
		stackTarjan.clear();
		splitSCC = false;
		nVisitedNodes = 0;
		for (int x = 0; x < arity; x++) {
			if (visitTime[x] < time)
				tarjanRemoveValues(x);
			Domain dom = scp[x].dom;
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int u = normalizedValueOf(dom.toVal(a));
				if (visitTime[arity + u] < time)
					tarjanRemoveValues(arity + u);
			}
		}
	}

	/**
	 * @param normalizedValue
	 *            : index between 0 and (maxDomainValue - minDomainValue). Domain values used in this class are normalized to use Sparse containers
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
	 * @return normalized value between 0 and (maxDomainValue - minDomainValue), corresponding to the domain value in parameter. Domain values used in this
	 *         class are normalized to use Sparse containers
	 */
	protected int normalizedValueOf(int domainValue) {
		return domainValue - minValue;
	}

	/**********************************************************************************************
	 * MatcherAllDifferent
	 *********************************************************************************************/

	/**
	 * Class used to perform GAC filtering in the AllDifferent constraint
	 */
	public static class MatcherAllDifferent extends Matcher {

		/**
		 * The variable each value is assigned to in the current matching
		 */
		private final int[] valToVar;

		public MatcherAllDifferent(AllDifferentComplete ctr) {
			super(ctr, ctr.scp);
			queueBFS = new SetSparse(arity);
			predBFS = Kit.repeat(-1, arity);
			valToVar = Kit.repeat(-1, intervalSize);
		}

		/**
		 * Finds a matching for the unmatched parameter variable while keeping the matched variables (may change the matched values though).
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
		 * Finds a matching for all the unmatched variables while keeping the matched variables (may change the matched values though).
		 * 
		 * @return true if a matching has been found, false otherwise (constraint unsatisfiable)
		 */
		@Override
		public boolean findMaximumMatching() {
			unmatchedVars.clear();
			for (int x = 0; x < arity; x++) {
				int u = varToVal[x];
				if (u == -1)
					unmatchedVars.add(x);
				else {
					assert valToVar[u] == x;
					if (!scp[x].dom.containsValue(domainValueOf(u))) {
						varToVal[x] = valToVar[u] = -1;
						unmatchedVars.add(x);
					}
					if (scp[x].dom.size() == 1 && unfixedVars.contains(x))
						unfixedVars.remove(x, ctr.problem.solver.depth());
				}
			}
			while (!unmatchedVars.isEmpty())
				if (!findMatchingFor(unmatchedVars.pop()))
					return false;
			// for (int x = 0; x < arity; x++)
			// System.out.println(x + "<->" + varToVal[x] + " " + valToVar[varToVal[x]]);
			return true;
		}

		/**
		 * Computes the neighbors of each value vertex and those of vertex T in the flow graph
		 */
		@Override
		protected void computeNeighbors() {
			for (SetSparse set : neighborsOfValues)
				set.clear();
			// Kit.control(neighborsOfT.isEmpty()); // not empty for a test case with queens. Should we clear?
			for (int x = 0; x < arity; x++) {
				Domain dom = scp[x].dom;
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					int u = normalizedValueOf(dom.toVal(a));
					if (valToVar[u] == x)
						neighborsOfValues[u].add(arity);
					else if (valToVar[u] != -1)
						neighborsOfT.remove(u);
					else {
						neighborsOfValues[u].remove(arity);
						neighborsOfT.add(u);
					}
					neighborsOfValues[u].add(x);
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
		private SetSparse[] possibleVars;

		/**
		 * Predecessor value of values in the DFS
		 */
		private int[] predValue;

		@Override
		public void restoreAtDepthBefore(int depth) {
			super.restoreAtDepthBefore(depth);
			// for (SetSparseReversible set : value2Variables) set.restore(depth);
		}

		@Override
		public void afterProblemConstruction() {
			super.afterProblemConstruction();
			// valToVars = IntStream.range(0, intervalSize).mapToObj(i -> new SetSparseReversible(arity, false, ctr.pb.variables.length + 1))
			// .toArray(SetSparseReversible[]::new);
			valToVars = IntStream.range(0, intervalSize).mapToObj(i -> new SetSparse(arity, false)).toArray(SetSparse[]::new);

		}

		/**
		 * @param ctr
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
		public MatcherCardinality(CardinalityConstant ctr, Variable[] scp, int[] keys, int[] minOccs, int[] maxOccs) {
			super(ctr, scp);
			this.keys = keys;

			this.minValue = Math.min(this.minValue, IntStream.of(keys).min().getAsInt());
			this.maxValue = Math.max(this.maxValue, IntStream.of(keys).max().getAsInt());
			this.intervalSize = maxValue - minValue + 1;

			// System.out.println("Interval " + this.intervalSize);

			queueBFS = new SetSparse(Math.max(arity, intervalSize));
			predBFS = Kit.repeat(-1, Math.max(arity, intervalSize));

			predValue = Kit.repeat(-1, intervalSize);

			this.minOccs = new int[intervalSize];
			this.maxOccs = Kit.repeat(Integer.MAX_VALUE, intervalSize);
			for (int i = 0; i < keys.length; i++) {
				this.minOccs[normalizedValueOf(keys[i])] = minOccs[i];
				this.maxOccs[normalizedValueOf(keys[i])] = maxOccs[i];
			}

			possibleVars = new SetSparse[intervalSize];
			for (int u = 0; u < intervalSize; u++) {
				possibleVars[u] = new SetSparse(arity);
				for (int x = 0; x < arity; x++)
					if (scp[x].dom.containsValue(domainValueOf(u)))
						possibleVars[u].add(x);
			}
		}

		private void handleAugmentingPath(int x, int u) { // , int currDepth) {
			while (predBFS[u] != -1) {
				int y = predBFS[u];
				varToVal[x] = u;
				valToVars[u].add(x); // , currDepth);
				valToVars[u].remove(y); // , currDepth);
				x = y;
				u = predValue[u];
			}
			varToVal[x] = u;
			valToVars[u].add(x);// , currDepth);
		}

		private boolean findMatchingForValue(int u) { // , int currDepth) {
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
							handleAugmentingPath(x, v); // , currDepth);
							return true;
						} else if (w != v) {
							if (valToVars[w].size() > minOccs[w] && varToVal[x] == w) {
								valToVars[w].remove(x); // IfPresent(x);
								handleAugmentingPath(x, v); // , currDepth);
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

		private boolean findMatchingForVariable(int x) { // , int currDepth) {
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
							valToVars[u].add(y); // , currDepth);
							valToVars[v].remove(y); // , currDepth);
							y = predBFS[y];
							u = v;
						}
						varToVal[y] = u;
						valToVars[u].add(y); // , currDepth);
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
							valToVars[u].remove(x); // , currDepth);
						if (maxOccs[v] == valToVars[v].size()) {
							varToVal[x] = -1;
						} else {
							varToVal[x] = v;
							valToVars[v].add(x); // , currDepth);
						}
					} else if (u != -1) {
						valToVars[u].remove(x); // , currDepth);
						varToVal[x] = -1;
					}
				}
			}
			// Generate a feasible flow (part of the matching)
			for (int i = 0; i < keys.length; i++) {
				int u = normalizedValueOf(keys[i]);
				while (valToVars[u].size() < minOccs[u])
					if (!findMatchingForValue(u)) // , currDepth))
						return false;
			}
			unmatchedVars.clear();
			for (int x = 0; x < arity; x++) {
				if (varToVal[x] == -1)
					unmatchedVars.add(x);
				else if (scp[x].dom.size() == 1 && unfixedVars.contains(x))
					unfixedVars.remove(x, ctr.problem.solver.depth()); // currDepth);
			}
			while (!unmatchedVars.isEmpty())
				if (!findMatchingForVariable(unmatchedVars.pop())) // , currDepth))
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
			Kit.control(IntStream.range(0, intervalSize)
					.allMatch(u -> IntStream.range(0, valToVars[u].size()).allMatch(i -> varToVal[valToVars[u].dense[i]] == u)));
			Kit.control(IntStream.range(0, arity).allMatch(x -> varToVal[x] == -1 || valToVars[varToVal[x]].contains(x)));
		}

		@SuppressWarnings("unused")
		private void checkMatchingValidity() {
			Kit.control(IntStream.range(0, arity).allMatch(x -> varToVal[x] != -1 && scp[x].dom.containsValue(domainValueOf(varToVal[x]))));
			Kit.control(IntStream.range(0, intervalSize).allMatch(u -> minOccs[u] <= valToVars[u].size() && valToVars[u].size() <= maxOccs[u]));
			checkMatchingConsistency();
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("varToVal : " + IntStream.of(varToVal).mapToObj(u -> domainValueOf(u) + " ").collect(Collectors.joining()));
			sb.append("\nvalue2Variables :\n");
			for (int u = 0; u < intervalSize; u++) {
				sb.append("Value " + domainValueOf(u) + " : ");
				for (int i = 0; i <= valToVars[u].limit; i++)
					sb.append(valToVars[u].dense[i] + " ");
				sb.append("\n");
			}
			sb.append("predVariable : " + Kit.join(predBFS) + "\n");
			// sb.append("found path : " + Kit.implode(foundPath) + "\n");
			return sb.toString();
		}
	}

}
