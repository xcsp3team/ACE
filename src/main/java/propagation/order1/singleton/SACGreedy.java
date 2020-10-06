/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.singleton;

import search.Solver;
import utility.Kit;
import variables.Variable;

public abstract class SACGreedy extends SAC {

	/**
	 * Metrics for greedy SAC approaches.
	 */
	public int nBranchesBuilt, sumBranchSizes;

	/**
	 * Parameters for tuning the greedy SAC approaches.
	 */
	protected boolean maximumBranchExtension = false, stopSACWhenFoundSolution = false; // hard coding

	/**
	 * The depth at which the first singleton check of each branch is performed.
	 */
	protected int nodeDepth;

	public SACGreedy(Solver solver) {
		super(solver);
	}

	protected boolean canFindAnotherExtensionInsteadOf(Variable x, int a) {
		if (solver.depth() == nodeDepth) // meaning that branchSize = 0
			return false;
		x.dom.removeElementary(a); // to avoid considering this value again when extending the branch
		return x.dom.size() == 0 ? false : enforceArcConsistencyAfterRefutation(x);
	}

	/**
	 * Actions to perform when a value has been detected non SAC.
	 */
	protected boolean manageInconsistentValue(Variable x, int a) {
		nEffectiveSingletonTests++;
		x.dom.removeElementary(a);
		if (shavingEvaluator != null)
			shavingEvaluator.updateRatioAfterShavingSuccess(x);
		if (x.dom.size() == 0)
			return false;
		assert queue.isEmpty();
		return enforceArcConsistencyAfterRefutation(x);
	}

	/**
	 * Restore the problem to the state it was before developing the branch.
	 */
	protected void eraseLastBuiltBranch(int branchSize) {
		nBranchesBuilt++;
		sumBranchSizes += branchSize;
		for (int i = 0; i < branchSize; i++) {
			Variable lastPast = solver.futVars.lastPast();
			solver.backtrack(lastPast);
			if (shavingEvaluator != null)
				shavingEvaluator.updateRatioAfterShavingFailure(lastPast);
		}
	}

	/**********************************************************************************************
	 * Experimental stuff below
	 *********************************************************************************************/

	protected ShavingEvaluator shavingEvaluator;

	class ShavingEvaluator {
		private static final double INCREMENT = 0.05;

		private double ratiosThreshold;

		private double[] sucessRatios;

		private int[] nFailuresSinceLastSuccess;

		private double alpha, beta;

		public double getSucessRatio(Variable x) {
			return sucessRatios[x.num];
		}

		public ShavingEvaluator(int nVariables, double alpha, double ratiosThreshold) {
			this.sucessRatios = Kit.repeat(1.0, nVariables);
			this.nFailuresSinceLastSuccess = new int[nVariables];
			this.ratiosThreshold = ratiosThreshold;
			this.alpha = alpha;
			this.beta = 1 - alpha;
			assert ratiosThreshold > 0 && ratiosThreshold < 1 && alpha > 0 && alpha < 1;
		}

		public boolean isEligible(Variable x) {
			return sucessRatios[x.num] >= ratiosThreshold;
		}

		public void updateRatioAfterShavingSuccess(Variable x) {
			sucessRatios[x.num] = sucessRatios[x.num] * alpha + beta; // * SUCCESS_VALUE
			nFailuresSinceLastSuccess[x.num] = 0;
		}

		public void updateRatioAfterShavingFailure(Variable x) {
			sucessRatios[x.num] = sucessRatios[x.num] * alpha; // + beta*FAILURE_VALUE
			nFailuresSinceLastSuccess[x.num]++;
		}

		public void updateRatioAfterUntest(Variable x) {
			sucessRatios[x.num] += INCREMENT / nFailuresSinceLastSuccess[x.num];
			// sucessRatios[variable.getId()] * alpha + beta * NEUTRAL_VALUE;
		}
	}
	/**********************************************************************************************
	 * End of experimental section
	 *********************************************************************************************/

}
