/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.partial;

import interfaces.TagExperimental;
import propagation.order1.singleton.SAC;
import search.Solver;
import variables.Variable;
import variables.domains.Domain;

public class SACPartial extends SAC implements TagExperimental {

	private final int[] residues; // 1D = variable id

	private PickThresholdManager pickThresholdManager;

	@Override
	public boolean propagate() {
		int nLocalPicks = 0;
		while (queue.size() != 0) {
			nLocalPicks++;
			if (!pickAndFilter())
				return false;
			if (pickThresholdManager != null && pickThresholdManager.mustStopPropagation(nLocalPicks))
				break;
		}
		return true;
	}

	public SACPartial(Solver solver) {
		super(solver);
		residues = new int[solver.pb.variables.length];
		cp().propagating.strongOnlyAtPreprocessing = false;
		if (cp().shaving.limitedPropagationSamplingSize >= 0)
			pickThresholdManager = new PickThresholdManager(250, cp().shaving.limitedPropagationSamplingSize);
	}

	private boolean isEligible(Variable x) {
		Domain dom = x.dom;
		if (dom.size() < 2)
			return false;
		int nDeletedElements = 0;
		long wsumOfDeletedElements = 0;
		int k = cp().shaving.parameter;
		int prevDepth = -1, depth = solver.depth(), stopDepth = depth < k ? -1 : depth - k;
		int delCntOfLevel = 0;
		for (int a = dom.lastRemoved(); a != -1 && dom.getRemovedLevelOf(a) > stopDepth; a = dom.prevRemoved(a)) {
			nDeletedElements++;
			if (dom.getRemovedLevelOf(a) != prevDepth) {
				wsumOfDeletedElements += delCntOfLevel * (k - depth + prevDepth);
				delCntOfLevel = 0;
				prevDepth = dom.getRemovedLevelOf(a);
			}
			delCntOfLevel++;
		}
		wsumOfDeletedElements += delCntOfLevel * (k - depth + prevDepth);
		double score = wsumOfDeletedElements / (double) (dom.size() + nDeletedElements);
		// if (score > GlobalData.shavingEligibilityThreshod)
		// System.out.println("score = " + score + " sum=" + weightedSumOfDroppedElements + " nb=" + nbDroppedElements);
		return score > cp().shaving.eligibilityThreshod;
	}

	@Override
	protected boolean checkSAC(Variable x, int a) {
		if (pickThresholdManager != null)
			pickThresholdManager.actBeforeSingletonCheck(queue.nPicks);
		boolean consistent = super.checkSAC(x, a);
		if (pickThresholdManager != null)
			pickThresholdManager.actAfterSingletonCheck(queue.nPicks, consistent);
		return consistent;
	}

	@Override
	protected int makeSingletonTestsOn(Variable x) {
		Domain dom = x.dom;
		int sizeBefore = dom.size();
		boolean mustStop = false;
		if (dom.isPresent(residues[x.num])) {
			mustStop = checkSAC(x, residues[x.num]);
			if (!mustStop)
				x.dom.removeElementary(residues[x.num]);
		}
		if (!mustStop) {
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				if (!checkSAC(x, a)) {
					x.dom.removeElementary(a);
					residues[x.num] = a;
				} else
					break;
			}
		}
		// System.out.println("sac of " + x + " give " + (sizeBefore - dom.size()) +
		// " removals at level " + (solver.getCurrentDepth() + 1));
		return sizeBefore - dom.size();
	}

	@Override
	protected boolean enforceStrongConsistency() {
		for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
			if (!isEligible(x))
				continue;
			if (makeSingletonTestsOn(x) > 0) {
				if (x.dom.size() == 0)
					return false;
				if (!enforceArcConsistencyAfterRefutation(x))
					return false;
			}
			if (solver.finished())
				return true;
		}
		return true;
	}
}
