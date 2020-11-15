/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.soft.pfc;

import java.util.stream.Stream;

import constraints.Constraint;
import interfaces.ObserverRuns;
import learning.LearnerNogoods;
import search.Solver;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

/**
 * TODO : s'assure qu'on dépase pas les upeprBound au niveau entre autres des sumMinCost (utiler pour les heuristiques de partition)
 * 
 * @author lecoutre
 * 
 */
public abstract class RDACAbstract extends PFC implements ObserverRuns {

	// !!!!!! problem with this class if nrr activated; works if -ln=no

	@Override
	public void beforeRun() {
		// go(false);
	}

	protected long timestamp;

	/** The value of minCosts[c][x][a] denotes the min cost for (x,a) in c. We use c.num, c.vapOf(x) and value index a. */
	public final long[][][] minCosts;

	public RDACAbstract(Solver solver) {
		super(solver);
		this.minCosts = Stream.of(solver.pb.constraints).map(c -> Variable.litterals(c.scp).longArray()).toArray(long[][][]::new);
	}

	@Override
	protected long computeMniOf(Variable x, boolean recomputeNbInconsistencies) {
		long ub = solver.solManager.bestBound;
		long[] t = sumMinCosts[x.num];
		int argMin = -1, argMax = -1;
		Domain dom = x.dom;
		for (int a = dom.first(); a != -1; a = dom.next(a)) {
			if (t[a] == -timestamp)
				t[a] = ub;
			else if (recomputeNbInconsistencies)
				t[a] = partitionOfConstraints.computeSumMinCostsOf(x, a);
			// else
			// Kit.control(t[a] == partitionOfConstraints.computeSumMinCostsOf(x, a));
			if (argMin == -1)
				argMin = argMax = a;
			else if (t[a] < t[argMin])
				argMin = a;
			else if (t[a] > t[argMax])
				argMax = a;
		}
		argMinSumMinCosts[x.num] = argMin;
		argMaxSumMinCosts[x.num] = argMax;
		return t[argMin];
	}

	protected abstract void updateStructuresFromRemovals();

	protected boolean filterDomains() {
		// System.out.println("start propagate");
		assert queue.size() == 0 && Kit.withNoNegativeValues(sumMinCosts);
		LearnerNogoods nm = ((SolverBacktrack) solver).learnerNogoods;
		Variable lastPast = solver.futVars.lastPast();
		boolean consistent = true; // lastPast == null || nm == null || nm.checkWatchesOf(lastPast, lastPast.dom.first(), false); // TO BE FIXED
		if (!consistent) {
			Kit.log.info("quick stop with nogood recording from restarts used");
			return false;
		}
		long ub = solver.solManager.bestBound;
		do {
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				long[] t = sumMinCosts[x.num];
				long base = Kit.addSafe(Kit.addSafe(partitionOfConstraints.distance, sumMnis), -t[argMinSumMinCosts[x.num]]);
				if (Kit.addSafe(base, t[argMaxSumMinCosts[x.num]]) < ub)
					continue;
				// from here, we have the guarantee to remove at least one value
				Domain dom = x.dom;
				// int sizeBefore = dom.size();
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					assert (t[a] == ub && controlMinCostEqualToUpperBound(x, a)) || t[a] == partitionOfConstraints.computeSumMinCostsOf(x, a);
					if (Kit.addSafe(Kit.addSafe(base, t[a]), computeOffset(x, a)) >= ub)
						dom.removeElementary(a);
				}
				// Kit.control(sizeBefore - dom.size() > 0); // BUG
				if (dom.size() == 0) {
					// x.wdeg++; //TODO how to do that, after refacoring od constraint weighting
					return false;
				}
				queue.add(x);
			}
			if (queue.size() == 0)
				return true;
			updateStructuresFromRemovals();
			// assert control();
			if (!computeSumMnis(false))
				return false;
		} while (true);

	}

	public void init(boolean incremental) {
		partitionOfConstraints.init(incremental);
		assert control();
	}

	public final boolean go(boolean incremental) {
		timestamp++;
		// if (partitionOfConstraints.distance + solver.getVariableManager().getNbFutureVariables() <
		// solver.solutionManager.getBestCostFound()) return true; // pas interessant pour l'heuristique de choix de valeurs
		init(incremental && solver.depth() > 1); // TODO a virer deuxime partie quand pb restart MRDAC regle
		// assert control();
		boolean consistent = computeSumMnis(true) && filterDomains();
		assert !consistent || control();
		return consistent;
	}

	@Override
	public boolean runInitially() {
		return go(false);
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		// if (!queue.isNogoodConsistent(x)) return false;// works only with nogood recording from restarts
		return go(true); // Data.branchingType != BranchingType.NON);
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		// if (!queue.isNogoodConsistent(x)) return false;
		return go(false);
	}

	private boolean controlMinCostEqualToUpperBound(Variable x, int a) {
		return Stream.of(x.ctrs).anyMatch(c -> minCosts[c.num][c.positionOf(x)][a] >= solver.solManager.bestBound);
	}

	public boolean control() {
		for (Constraint c : solver.pb.constraints)
			for (Variable x : c.scp)
				if (!x.isAssigned()) {
					for (int a = x.dom.first(); a != -1; a = x.dom.next(a)) {
						long v = c.seekFirstSupportWith(c.positionOf(x), a) ? 0 : c.cost;
						Kit.control(Math.min(v, solver.solManager.bestBound) == minCosts[c.num][c.positionOf(x)][a],
								() -> "Recomputed value is different from stored value");
					}
				}
		return true;
	}
}
