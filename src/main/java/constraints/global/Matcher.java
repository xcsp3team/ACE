package constraints.global;

import java.util.stream.Stream;

import constraints.Constraint;
import interfaces.ObserverConstruction;
import sets.SetSparse;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public abstract class Matcher implements ObserverConstruction {

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

		ctr.pb.rs.observersConstruction.add(this);

		// TODO use classical sets (not sparse sets or arrays) if big gap between
		// minValue and maxValue AND number of values is a lot smaller than maxValue-minValue
	}

	@Override
	public void onConstructionProblemFinished() {
		unfixedVars = new SetSparseReversible(arity, ctr.pb.variables.length + 1);

		neighborsOfValues = SetSparse.factoryArray(arity + 1, intervalSize);
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
			if (stackTarjan.isPresent(adjacentNode) && numDFS[adjacentNode] < lowLink[node])
				lowLink[node] = numDFS[adjacentNode];
		} else {
			tarjanRemoveValues(adjacentNode);
			if (lowLink[adjacentNode] < lowLink[node])
				lowLink[node] = lowLink[adjacentNode];
		}
	}

	/**
	 * Computes Tarjan algorithm and prunes some values from the domains. Nodes are given a number as follows: a) i for the ith variable of the scope,
	 * b) arity+v for a value v between minValue and maxValue, c) arity+intervalSize for node T
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
							int a = scp[x].dom.toPresentIdx(domainValueOf(u));
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
	 * Finds the strongly connected components of the flow graph as defined in Ian P. Gent, Ian Miguel, and Peter Nightingale, The AllDifferent
	 * Constraint: An Empirical Survey, and prunes the domains to reach GAC
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
	 * @return normalized value between 0 and (maxDomainValue - minDomainValue), corresponding to the domain value in parameter. Domain values used in
	 *         this class are normalized to use Sparse containers
	 */
	protected int normalizedValueOf(int domainValue) {
		return domainValue - minValue;
	}
}
