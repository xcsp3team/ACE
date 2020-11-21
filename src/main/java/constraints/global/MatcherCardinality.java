package constraints.global;

import java.util.stream.Collectors;
import java.util.stream.IntStream;

import constraints.global.Cardinality.CardinalityConstant;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public class MatcherCardinality extends Matcher {

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
				if (scp[x].dom.isPresentValue(domainValueOf(u)))
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
				if (dom.isPresentValue(domainValueOf(v))) {
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
				} else {
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
		}
		return false;
	}

	@Override
	public boolean findMaximumMatching() {
		// Make sure each variable is not matched with a value that is not in its domain anymore
		for (int x = 0; x < arity; x++) {
			Domain dom = scp[x].dom;
			int u = varToVal[x];
			if (u == -1 || !dom.isPresentValue(domainValueOf(u))) {
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
			else if (scp[x].dom.size() == 1 && unfixedVars.isPresent(x))
				unfixedVars.remove(x, ctr.pb.solver.depth()); // currDepth);
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
				if (scp[x].dom.isPresentValue(domainValueOf(u)) && varToVal[x] != u)
					neighborsOfValues[u].add(x);
				else
					neighborsOfValues[u].remove(x);
			}
		}
	}

	private void checkMatchingConsistency() {
		Kit.control(
				IntStream.range(0, intervalSize).allMatch(u -> IntStream.range(0, valToVars[u].size()).allMatch(i -> varToVal[valToVars[u].dense[i]] == u)));
		Kit.control(IntStream.range(0, arity).allMatch(x -> varToVal[x] == -1 || valToVars[varToVal[x]].isPresent(x)));
	}

	@SuppressWarnings("unused")
	private void checkMatchingValidity() {
		Kit.control(IntStream.range(0, arity).allMatch(x -> varToVal[x] != -1 && scp[x].dom.isPresentValue(domainValueOf(varToVal[x]))));
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
