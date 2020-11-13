package constraints.global;

import sets.SetSparse;
import utility.Kit;
import variables.domains.Domain;

/**
 * Class used to perform GAC filtering in the AllDifferent constraint
 */
public class MatcherAllDifferent extends Matcher {

	/**
	 * The variable each value is assigned to in the current matching
	 */
	private final int[] valToVar;

	public MatcherAllDifferent(AllDifferent ctr) {
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
				if (!scp[x].dom.isPresentValue(domainValueOf(u))) {
					varToVal[x] = valToVar[u] = -1;
					unmatchedVars.add(x);
				}
				if (scp[x].dom.size() == 1 && unfixedVars.isPresent(x))
					unfixedVars.remove(x, ctr.pb.solver.depth());
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
