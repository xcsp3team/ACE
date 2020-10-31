/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.soft.pfc;

import constraints.Constraint;
import search.Solver;
import variables.Variable;
import variables.domains.Domain;

public class PRDAC extends RDAC {

	private long[] offsetOfMinNbDetectedInconsistencies;

	// private boolean[] traite;

	public PRDAC(Solver solver) {
		super(solver);
		offsetOfMinNbDetectedInconsistencies = new long[solver.pb.variables.length];
		// traite = new boolean[constraints.length];
	}

	@Override
	protected long computeMniOf(Variable x, boolean recomputeNbInconsistencies) {
		long[] t = sumMinCosts[x.num];
		Domain dom = x.dom;
		long offset = Long.MAX_VALUE;
		int argMin = -1, argMax = -1;
		for (int a = dom.first(); a != -1; a = dom.next(a)) {
			if (recomputeNbInconsistencies)
				t[a] = partitionOfConstraints.computeSumMinCostsOf(x, a);
			if (argMin == -1)
				argMin = argMax = a;
			else if (t[a] < t[argMin]) {
				argMin = a;
				offset = t[argMin] - t[a];
			} else {
				if (t[a] > t[argMax])
					argMax = a;
				offset = Math.min(offset, t[a] - t[argMin]);
			}
		}
		if (offset == Long.MAX_VALUE)
			offset = 0;
		// System.out.println("offset = " + offset);
		argMinSumMinCosts[x.num] = argMin;
		offsetOfMinNbDetectedInconsistencies[x.num] = offset;
		argMaxSumMinCosts[x.num] = argMax;
		return t[argMin];
	}

	// protected int computeMniOf(Variable variable, boolean mustComputeNbViolatedConstraints) {
	// int[] t = nbInconsistencies[variable.getId()];
	//
	// Elements elements = variable.domain.getElements();
	// int offset = Integer.MAX_VALUE;
	// int bestMinIndex = elements.getFirstPresent();
	// int bestMaxIndex = bestMinIndex;
	// if (mustComputeNbViolatedConstraints)
	// t[bestMinIndex] = partitionOfConstraints.computeNbInconsistenciesFor(variable, bestMinIndex);
	// for (int index = elements.getNextPresent(bestMinIndex); index != -1; index = elements.getNextPresent(index)) {
	// if (mustComputeNbViolatedConstraints)
	// t[index] = partitionOfConstraints.computeNbInconsistenciesFor(variable, index);
	//
	// if (t[index] < t[bestMinIndex]) {
	// bestMinIndex = index;
	// offset = t[bestMinIndex] - t[index];
	// } else {
	// if (t[index] > t[bestMaxIndex])
	// bestMaxIndex = index;
	// offset = Math.min(offset, t[index] - t[bestMinIndex]);
	// }
	// }
	// minNbInconsistenciesIndex[variable.getId()] = bestMinIndex;
	// offsetOfMinNbDetectedInconsistencies[variable.getId()] = offset;
	// maxNbInconsistenciesIndex[variable.getId()] = bestMaxIndex;
	// return t[bestMinIndex];
	// }

	@SuppressWarnings("unused")
	private long compute(Variable x) {
		long[] t = sumMinCosts[x.num];
		int bestIndex = argMinSumMinCosts[x.num];
		long best = t[bestIndex];
		long bestOffset = Long.MAX_VALUE;
		Domain dom = x.dom;
		for (int a = dom.first(); a != -1; a = dom.next(a)) {
			if (a == bestIndex)
				continue;
			long offset = t[a] - best;
			if (offset < bestOffset) {
				bestOffset = offset;
				if (bestOffset == 0)
					return 0;
			}
		}
		return bestOffset;
	}

	@Override
	protected long computeOffset(Variable x, int a) {
		long cnt = 0;
		for (Variable y = solver.futVars.first(); y != null; y = solver.futVars.next(y)) {
			if (x == y)
				continue;
			// int v = compute(futureVariable);
			// if (v < offsetOfMinNbDetectedInconsistencies[futureVariable.id])
			// System.out.println("strange v=" + v + " off=" + offsetOfMinNbDetectedInconsistencies[futureVariable.id]);
			// if (v == 0) continue;

			if (offsetOfMinNbDetectedInconsistencies[y.num] == 0)
				continue;
			Constraint c = x.firstBinaryConstraintWith(y);
			if (c == null)
				continue;
			if (partitionOfConstraints.membership[c.num] != y.num)
				continue;
			int b = argMinSumMinCosts[y.num];
			int p = c.positionOf(y);
			if (minCosts[c.num][p][b] > 0)
				continue;
			int[] tmp = c.tupleManager.localTuple;
			tmp[p] = b;
			tmp[p == 1 ? 0 : 1] = a;
			if (!c.checkIndexes(tmp))
				cnt += c.cost;
		}
		return cnt;
	}

	// public long getNbInconcistenciesOf(Variable x, int idx) {
	// return nbInconsistencies[x.num][idx] + computeOffset(x, idx);
	// }
}
