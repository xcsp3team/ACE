/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.soft.pfc;

import propagation.order1.AC;
import propagation.soft.LowerBoundCapability;
import search.Solver;
import utility.Enums.EBranching;
import utility.Kit;
import utility.operations.Calculator;
import variables.Variable;

public abstract class PFC extends AC implements LowerBoundCapability {

	@Override
	public final long getLowerBound() {
		return partitionOfConstraints.distance;
	}

	protected PartitionOfConstraints partitionOfConstraints;

	/**
	 * sumMinCosts[x][a] is the sum of the min costs of (x,a) when considering the current partition ; something equivalent to ic_ia + dac_ia
	 */
	public long[][] sumMinCosts;

	/**
	 * argSumMinCosts[x] gives the idx corresponding to the minimum sum of the min costs for the variable
	 */
	public int[] argMinSumMinCosts;

	protected int[] argMaxSumMinCosts;

	protected long sumMnis;

	public PFC(Solver solver) {
		super(solver);
		Kit.control(cp().settingSolving.branching != EBranching.NON, () -> "Non-binary branching not possible for WCSP or MaxCSP");
		sumMinCosts = Variable.litterals(solver.pb.variables).longArray();
		argMinSumMinCosts = new int[solver.pb.variables.length];
		argMaxSumMinCosts = new int[solver.pb.variables.length];
	}

	protected abstract long computeMniOf(Variable x, boolean recomputeNbInconsistencies);

	protected boolean computeSumMnis(boolean recomputeNbInconsistencies) {
		sumMnis = 0;
		Variable greatestImpactVariable = null;
		long greatestImpact = -1;
		long ub = solver.solManager.bestBound;
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			sumMnis = Calculator.add(sumMnis, computeMniOf(x, recomputeNbInconsistencies));
			long impact = sumMinCosts[x.num][argMinSumMinCosts[x.num]];
			if (impact > greatestImpact) {
				greatestImpactVariable = x;
				greatestImpact = impact;
			}
			if (Calculator.add(partitionOfConstraints.distance, sumMnis) >= ub) {
				// greatestImpactVariable.wdeg++; // TODO how to do that, after refactoring of constraint weighting
				return false;
			}
		}
		return true;
	}

	protected long computeOffset(Variable x, int a) {
		return 0;
	}
}
