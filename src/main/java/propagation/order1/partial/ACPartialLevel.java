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
import utility.Kit;
import variables.Variable;

public class ACPartialLevel extends SAC implements TagExperimental {

	private PickThresholdManager[] pickThresholdManagers;

	public int[][] effectifFalse; // 1D = level; 2D=length of propagation; value= effectif
	public int[][] effectifTrue;

	public boolean displayEffectif = false;

	@Override
	public boolean propagate() {
		int nLocalPicks = 0;
		int depth = solver.depth();

		boolean collectStats = false; // displayEffectif && queue.size() == 1 && queue.getVariable(0).isAssigned() &&
										// (queue.getVariable(0).domain.getElements().getLastDroppedLevel() ==
										// solver.getCurrentDepth());
		while (queue.size() != 0) {
			nLocalPicks++;
			boolean consistent = pickAndFilter();
			if (!consistent) {
				if (collectStats) {
					// System.out.println(nbLocalPicks + " " + false);
					effectifFalse[depth][nLocalPicks]++;
				}
				return false;
			}
			if (pickThresholdManagers != null && pickThresholdManagers[depth].mustStopPropagation(nLocalPicks)) {
				break;
			}
		}
		if (collectStats)
			effectifTrue[depth][nLocalPicks]++;
		return true;
	}

	@Override
	public boolean runAfterAssignment(Variable x) {
		int level = this.solver.depth();
		if (pickThresholdManagers != null)
			pickThresholdManagers[level].actBeforeSingletonCheck(queue.nPicks);
		boolean b = super.runAfterAssignment(x);
		if (pickThresholdManagers != null)
			pickThresholdManagers[level].actAfterSingletonCheck(queue.nPicks, b);
		return b;
	}

	public ACPartialLevel(Solver solver) {
		super(solver);
		int length = 250, nbVariables = solver.pb.variables.length;
		if (cp().settingShaving.limitedPropagationSamplingSize >= 0) {
			pickThresholdManagers = new PickThresholdManager[nbVariables + 1];
			for (int i = 0; i < pickThresholdManagers.length; i++)
				pickThresholdManagers[i] = new PickThresholdManager(length, cp().settingShaving.limitedPropagationSamplingSize);
		}
		if (displayEffectif) {
			effectifTrue = new int[nbVariables + 1][length];
			effectifFalse = new int[nbVariables + 1][length];
		}
	}

	@Override
	protected boolean enforceStrongConsistency() {
		return true;
	}

	public void display() {
		if (displayEffectif) {
			System.out.println();
			System.out.println(solver.pb.name());
			for (int i = 0; i < effectifFalse.length; i++) {
				if (Kit.sum(effectifFalse[i]) == 0 && Kit.sum(effectifTrue[i]) == 0)
					continue;
				System.out.println("LEVEL " + i + " false (nb=" + Kit.sum(effectifFalse[i]) + ",avg=" + Kit.computeAveragePositionOf(effectifFalse[i])
						+ ") => " + Kit.join(effectifFalse[i]));
				System.out.println("                           true (nb=" + Kit.sum(effectifTrue[i]) + ",avg="
						+ Kit.computeAveragePositionOf(effectifTrue[i]) + ") => " + Kit.join(effectifTrue[i]));
			}
		}
	}
}
