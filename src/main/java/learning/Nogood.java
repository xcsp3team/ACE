/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package learning;

import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import solver.Decisions;
import utility.Kit;

/**
 * Strictly speaking, an object of this class denotes a nogood constraint, i.e. a disjunction of negative decisions that must be enforced (to be true).
 */
public final class Nogood {

	public final int[] literals; // only negative literals (decisions) since a classical nogood

	private int watch1, watch2;

	public int getWatchedPosition(boolean firstWatch) {
		return firstWatch ? watch1 : watch2;
	}

	public int getWatchedDecision(boolean firstWatch) {
		return literals[firstWatch ? watch1 : watch2];
	}

	public void setWatchedPosition(int position, boolean firstWatch) {
		if (firstWatch)
			watch1 = position;
		else
			watch2 = position;
	}

	public boolean isPositionWatched(int position) {
		return watch1 == position || watch2 == position;
	}

	public boolean isDecisionWatched(int decision) {
		return literals[watch1] == decision || literals[watch2] == decision;
	}

	public boolean isDecisionWatchedByFirstWatch(int watchedDecision) {
		assert isDecisionWatched(watchedDecision);
		return literals[watch1] == watchedDecision;
	}

	public int getSecondWatchedDecision(int watchedDecision) {
		assert isDecisionWatched(watchedDecision);
		return literals[watch1] == watchedDecision ? literals[watch2] : literals[watch1];
	}

	public Nogood(int[] decisions) {
		Kit.control(decisions.length > 1 && Arrays.stream(decisions).noneMatch(d -> d >= 0));
		this.literals = decisions;
		this.watch1 = 0;
		this.watch2 = decisions.length - 1;
	}

	public String toString(Decisions decisions) {
		return IntStream.of(literals).mapToObj(d -> decisions.varIn(d) + (d < 0 ? "!=" : "=") + decisions.valIn(d)).collect(Collectors.joining(" "));
	}
}
