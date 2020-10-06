/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1.partial;

public class PickThresholdManager {
	private int[] nFailedOccurrencesByNbPicks; // 1D = propagation length (nb picks in queue during propagation) ;
												// value = nb times of propagation with this length (for index 0, nb

	// times of propagation with a length >=nbFailedOccurrencesByPropagationLengths.length

	private int[] nSucceedOccurrencesByNbPicks; // 1D = propagation length (nb picks in queue during propagation) ;
													// value = nb times of propagation with this length

	private int[] sample;

	private int sampleCursor;

	private int cycleLength = 10; // hard coding

	private int cycleCursor;

	private boolean initializationPhase = true;

	private int pickThreshold = Integer.MAX_VALUE;

	private boolean singletonCheckRunning;

	private boolean alwaysLimitPropagationLength = false; // hard coding

	private int nPicksBefore;

	public boolean mustStopPropagation(int nbPicks) {
		return (singletonCheckRunning || alwaysLimitPropagationLength) && nbPicks >= pickThreshold;
	}

	PickThresholdManager(int initialThreshold, int sampleSize) {
		nFailedOccurrencesByNbPicks = new int[initialThreshold];
		nSucceedOccurrencesByNbPicks = new int[initialThreshold];
		sample = new int[sampleSize];
		pickThreshold = initialThreshold - 1;
	}

	public void actBeforeSingletonCheck(int nbPicks) {
		singletonCheckRunning = true;
		nPicksBefore = nbPicks;
		if (!initializationPhase && ++cycleCursor == cycleLength)
			pickThreshold = Integer.MAX_VALUE;
	}

	private void addData(boolean consistent, int nAchievedPicks) {
		if (!consistent) {
			if (nAchievedPicks >= nFailedOccurrencesByNbPicks.length) {
				nFailedOccurrencesByNbPicks[0]++;
				sample[sampleCursor] = Integer.MIN_VALUE;
			} else {
				nFailedOccurrencesByNbPicks[nAchievedPicks]++;
				sample[sampleCursor] = -nAchievedPicks;
			}
		} else {
			if (nAchievedPicks >= nSucceedOccurrencesByNbPicks.length) {
				nSucceedOccurrencesByNbPicks[0]++;
				sample[sampleCursor] = Integer.MAX_VALUE;
			} else {
				nSucceedOccurrencesByNbPicks[nAchievedPicks]++;
				sample[sampleCursor] = nAchievedPicks;
			}
		}
		sampleCursor = (sampleCursor + 1) % sample.length;
	}

	private void computeNewThreshold() {
		int nbCurrentFailedOccurrences = 0, nbCurrentSucceedOccurrences = 0;
		long sumCurrentFailedOccurrences = 0, sumCurrentSucceedOccurrences = 0;
		double bestCost = Double.MAX_VALUE;
		int bestNbPicks = 0;
		for (int i = 1; i < nFailedOccurrencesByNbPicks.length; i++) {
			nbCurrentSucceedOccurrences += nSucceedOccurrencesByNbPicks[i];
			sumCurrentSucceedOccurrences += i * nSucceedOccurrencesByNbPicks[i];
			if (nFailedOccurrencesByNbPicks[i] != 0) {
				nbCurrentFailedOccurrences += nFailedOccurrencesByNbPicks[i];
				sumCurrentFailedOccurrences += i * nFailedOccurrencesByNbPicks[i];
				double currentCost = sumCurrentFailedOccurrences + sumCurrentSucceedOccurrences + i
						* (sample.length - nbCurrentFailedOccurrences - nbCurrentSucceedOccurrences);
				double averageCost = currentCost / nbCurrentFailedOccurrences; // (nbCurrentFailedOccurrences *
																				// nbCurrentFailedOccurrences);
				if (averageCost < bestCost) {
					bestNbPicks = i;
					bestCost = averageCost;
					// System.out.println("better pick " + i + " cost=" + bestCost);
				}
			}
			if (nbCurrentFailedOccurrences + nbCurrentSucceedOccurrences == sample.length)
				break;
		}
		pickThreshold = bestNbPicks;
		display();
	}

	public void actAfterSingletonCheck(int nbPicks, boolean consistent) {
		singletonCheckRunning = false;
		// System.out.println(nbAchievedPicks + " " + consistent + " " + solver.getCurrentDepth());
		if (initializationPhase) {
			addData(consistent, nbPicks - nPicksBefore);
			if (sampleCursor == 0)
				initializationPhase = false;
		} else if (cycleCursor == cycleLength) {
			assert pickThreshold == Integer.MAX_VALUE;
			cycleCursor = 0;
			// remove old data at sampleCursor
			if (sample[sampleCursor] < 0) {
				if (sample[sampleCursor] == Integer.MIN_VALUE)
					nFailedOccurrencesByNbPicks[0]--;
				else
					nFailedOccurrencesByNbPicks[-sample[sampleCursor]]--;
			} else {
				if (sample[sampleCursor] == Integer.MAX_VALUE)
					nSucceedOccurrencesByNbPicks[0]--;
				else
					nSucceedOccurrencesByNbPicks[sample[sampleCursor]]--;
			}
			addData(consistent, nbPicks - nPicksBefore);
			computeNewThreshold();
		}
	}

	private void display() {
		// System.out.println("\n failed : " + Toolkit.buildStringFromInts(nbFailedOccurrencesByNbPicks));
		// System.out.println("\n success : " + Toolkit.buildStringFromInts(nbSucceedOccurrencesByNbPicks));
		// System.out.println("pick = " + pickThreshold);
		// System.out.println(pickThreshold);
	}
}