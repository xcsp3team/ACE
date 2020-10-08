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

public class ACPartial extends SAC implements TagExperimental {

	private PickThresholdManager pickThresholdManager;

	public int[] effectifFalseACPartial;
	public int[] effectifTrueACPartial;

	public boolean displayEffectif = false; // true;

	@Override
	public boolean propagate() {
		int nbLocalPicks = 0;

		boolean collectStats = true; // false; // displayEffectif && queue.size() == 1 &&
										// queue.getVariable(0).isAssigned() &&
										// (queue.getVariable(0).domain.getElements().getLastDroppedLevel() ==
		// solver.getCurrentDepth());
		// boolean displayMouny = false; // true; // singletonCheckRunning;
		// int nbValuesBefore = Domain.getNbValuesRemoved(); //, nbRemovedAtFirstPick = -1;
		while (queue.size() != 0) {
			nbLocalPicks++;
			boolean consistent = pickAndFilter();
			// if (nbLocalPicks == 1) nbRemovedAtFirstPick = Domain.getNbValuesRemoved() - nbValuesBefore;
			if (!consistent) {
				if (collectStats) {
					System.out.println(nbLocalPicks + " " + false); // + " " + nbRemovedAtFirstPick + " " +
																	// nbValuesInNeighbourhood + " " + (100 *
																	// nbRemovedAtFirstPick) / nbValuesInNeighbourhood);
					// effectifFalse[nbLocalPicks]++;
				}
				// GraphvizSaver.saveGraph(this.solver.problem);
				return false;
			}
			if (pickThresholdManager != null && pickThresholdManager.mustStopPropagation(nbLocalPicks)) {
				break;
			}
			// if (this.solver.getCurrentDepth() == 1)
			// GraphvizSaver.saveGraph(this.solver.problem);
		}
		if (collectStats) {
			System.out.println(nbLocalPicks + " " + true); // + " " + nbRemovedAtFirstPick + " " +
															// nbValuesInNeighbourhood + " " + (100 *
															// nbRemovedAtFirstPick) / nbValuesInNeighbourhood);
			// effectifTrue[nbLocalPicks]++;
		}
		return true;
	}

	@Override
	public boolean runAfterAssignment(Variable var) {
		if (pickThresholdManager != null)
			pickThresholdManager.actBeforeSingletonCheck(queue.nPicks);
		boolean b = super.runAfterAssignment(var);
		if (pickThresholdManager != null)
			pickThresholdManager.actAfterSingletonCheck(queue.nPicks, b);
		return b;
	}

	public ACPartial(Solver solver) {
		super(solver);
		int length = 250;
		if (cp().settingShaving.limitedPropagationSamplingSize >= 0)
			pickThresholdManager = new PickThresholdManager(length, cp().settingShaving.limitedPropagationSamplingSize);
		if (displayEffectif) {
			effectifTrueACPartial = new int[length];
			effectifFalseACPartial = new int[length];
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
			System.out.println("false (nb=" + Kit.sum(effectifFalseACPartial) + ",avg=" + Kit.computeAveragePositionOf(effectifFalseACPartial) + ") => "
					+ Kit.join(effectifFalseACPartial));
			System.out.println("true (nb=" + Kit.sum(effectifTrueACPartial) + ",avg=" + Kit.computeAveragePositionOf(effectifTrueACPartial) + ") => "
					+ Kit.join(effectifTrueACPartial));
		}
	}
}

// public int[] statistics {
// return pickThresholdManager.statistics;
// }

// private class PickThresholdManager {
// private int[] nbWOs; // 1D = propagation length (nb picks in queue during propagation) ; value = nb times of
// propagation with this length (for index 0, nb times of propagation with a length
//
// // >=nbWOs.length
//
// private int[] nbFPs; // 1D = propagation length (nb picks in queue during propagation) ; value = nb times of
// propagation with this length
//
// private int nbTotalWOs;
//
// private int nbTotalFPs;
//
// private int nbTotalUnknowns;
//
// private int collectingLimit;
//
// private int pickThreshold; // =4;
//
// private int nbPicksBefore;
//
// int lastPickThresholdBeforeReduction;
//
// private boolean lastCheckUnknown;
//
// private PickThresholdManager(int initialThreshold, int collectingLimit) {
// nbWOs = new int[initialThreshold];
// nbFPs = new int[initialThreshold];
// this.collectingLimit = collectingLimit;
// pickThreshold = initialThreshold - 1;
// }
//
// private void actBeforeSingletonCheck() {
// // queue.size() == 1 && queue.getVariable(0).isAssigned()&&
// (queue.getVariable(0).domain.getElements().getLastDroppedLevel() ==
// // solver.getCurrentDepth());
// nbPicksBefore = queue.getNbPicks();
// lastCheckUnknown = false;
// }
//
// private void incrementNbUnknowns() {
// lastCheckUnknown = true;
// }
//
// private int searchFirstNonZeroSucceedOccurrences() {
// for (int i = 1; i < nbFPs.length; i++)
// if (nbFPs[i] > 0)
// return i;
// return nbFPs.length - 1;
// }
//
// public int[] statistics {
// int[] t = new int[4];
// t[0] = nbTotalWOs;
// t[1] = nbTotalFPs;
// double sum = 0;
// for (int i = 1; i < nbWOs.length; i++)
// sum += (i * nbWOs[i]);
// t[2] = nbTotalWOs == 0 ? -1 : (int) sum / nbTotalWOs;
// sum = 0;
// for (int i = 1; i < nbFPs.length; i++)
// sum += (i * nbFPs[i]);
// t[3] = nbTotalFPs == 0 ? -1 : (int) sum / nbTotalFPs;
// //display();
// return t;
//
// }
//
// private void actAfterSingletonCheck(boolean consistent) {
// int nbAchievedPicks = queue.getNbPicks() - nbPicksBefore;
// if (nbAchievedPicks == 1)
// return;
//
// if (lastCheckUnknown)
// nbTotalUnknowns++;
// else if (!consistent) {
// nbWOs[nbAchievedPicks >= nbWOs.length ? 0 : nbAchievedPicks]++;
// nbTotalWOs++;
// } else {
// nbFPs[nbAchievedPicks >= nbFPs.length ? 0 : nbAchievedPicks]++;
// nbTotalFPs++;
// }
// if (nbTotalWOs + nbTotalFPs + nbTotalUnknowns >= collectingLimit) {
// if (nbTotalWOs == 0)
// pickThreshold = searchFirstNonZeroSucceedOccurrences();
// else {
// int nbCurrentFailedOccurrences = 0, nbCurrentSucceedOccurrences = 0;
// long sumCurrentFailedOccurrences = 0, sumCurrentSucceedOccurrences = 0;
// double bestCost = Double.MAX_VALUE;
// int bestNbPicks = -1;
// for (int i = 1; i <= pickThreshold; i++) {
// nbCurrentFailedOccurrences += nbWOs[i];
// sumCurrentFailedOccurrences += i * nbWOs[i];
// nbCurrentSucceedOccurrences += nbFPs[i];
// sumCurrentSucceedOccurrences += i * nbFPs[i];
// if (nbWOs[i] == 0)
// continue;
// double currentCost = nbTotalUnknowns * i + sumCurrentFailedOccurrences + sumCurrentSucceedOccurrences + i *
// (nbTotalWOs - nbCurrentFailedOccurrences + nbTotalFPs - nbCurrentSucceedOccurrences);
// double averageCost = currentCost / nbCurrentFailedOccurrences;
// // double averageCost = currentCost / (nbCurrentFailedOccurrences * nbCurrentFailedOccurrences);
// if (averageCost < bestCost) {
// bestNbPicks = i;
// bestCost = averageCost;3

// }
// }
//
// if (bestNbPicks == pickThreshold) {
// // System.out.println(pickThreshold + " "+lastPickThresholdBeforeReduction);
// int increment = 1; // + (GlobalData.shavingLimitedPropagationThresholdEvolutionMode &&
// lastPickThresholdBeforeReduction > pickThreshold ? (lastPickThresholdBeforeReduction -
// // pickThreshold) / 2 : 0);
// pickThreshold = Math.min(pickThreshold + increment, nbWOs.length - 1);
// } else {
// lastPickThresholdBeforeReduction = pickThreshold;
// pickThreshold = bestNbPicks;
// }
// // pickThreshold = 3;
// //display();
// // System.out.println("best= " + bestNbPicks + " " + bestCost + " newThreshold=" + pickThreshold + " lastPick=" +
// lastPickThresholdBeforeReduction + " nbUnk=" + nbTotalUnknowns);
// reset();
// }
// }
// }

// private void reset() {
// Arrays.fill(nbWOs, 0);
// Arrays.fill(nbFPs, 0);
// nbTotalWOs = nbTotalFPs = nbTotalUnknowns = 0;
// }
//
// private void display() {
// System.out.println("\n failed : " + Toolkit.buildStringFromInts(nbWOs) + " (" + nbTotalWOs + ")");
// System.out.println("\n success : " + Toolkit.buildStringFromInts(nbFPs) + " (" + nbTotalFPs + ")");
// }
//
// }
