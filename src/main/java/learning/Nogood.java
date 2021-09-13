/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package learning;

import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import solver.Decisions;
import utility.Kit;

/**
 * Strictly speaking, an object of this class is used as if it was a nogood constraint, i.e. a disjunction of negative decisions that must be enforced (to be
 * true). However, nogoods are handled apart during constraint propagation.
 * 
 * @author Christophe Lecoutre
 */
public final class Nogood {

	/**
	 * The negative literals (decisions) of the nogood (since it is a classical nogood)
	 */
	public final int[] literals;

	/**
	 * The first watch on the nogood, that is to say the position of a literal that can still be satisfied
	 */
	private int watch1;

	/**
	 * The second watch on the nogood, that is to say the position of a literal that can still be satisfied
	 */
	private int watch2;

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

	/**
	 * Builds a nogood from the specified literals (negative decisions)
	 * 
	 * @param negativeDecisions
	 *            the negative decisions (literals) forming the nogood
	 */
	public Nogood(int[] negativeDecisions) {
		Kit.control(negativeDecisions.length > 1 && Arrays.stream(negativeDecisions).noneMatch(d -> d >= 0));
		this.literals = negativeDecisions;
		this.watch1 = 0;
		this.watch2 = negativeDecisions.length - 1;
	}

	public String toString(Decisions decisions) {
		return IntStream.of(literals).mapToObj(d -> decisions.varIn(d) + (d < 0 ? "!=" : "=") + decisions.valIn(d)).collect(Collectors.joining(" "));
	}
}
