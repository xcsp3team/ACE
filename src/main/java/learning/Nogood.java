/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package learning;

import static utility.Kit.control;

import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import solver.Decisions;

/**
 * Strictly speaking, an object of this class is used as if it was a nogood constraint, i.e. a disjunction of negative
 * decisions that must be enforced (to be true). However, nogoods are handled apart during constraint propagation.
 * 
 * @author Christophe Lecoutre
 */
public final class Nogood {

	/**
	 * The negative literals (decisions) of the nogood (since it is a classical nogood)
	 */
	public final int[] decisions;

	/**
	 * The first watch on the nogood, that is to say the index of a decision that can still be satisfied
	 */
	private int watch1;

	/**
	 * The second watch on the nogood, that is to say the index of a decision that can still be satisfied
	 */
	private int watch2;

	/**
	 * @param first
	 *            true if the first watch is concerned, false for the second one
	 * @return the first or second watch according to the value of the specified Boolean
	 */
	public int getWatch(boolean first) {
		return first ? watch1 : watch2;
	}

	/**
	 * @return the first watched decision
	 */
	public int firstWatchedDecision() {
		return decisions[watch1];
	}

	/**
	 * @return the second watched decision
	 */
	public int secondWatchedDecision() {
		return decisions[watch2];
	}

	/**
	 * Sets the specified value (index of decision) for the watch identified by the specified Boolean
	 * 
	 * @param index
	 *            the value of the watch (index of a decision)
	 * @param first
	 *            true if the first watch is concerned, false for the second one
	 */
	public void setWatch(int index, boolean first) {
		if (first)
			watch1 = index;
		else
			watch2 = index;
	}

	/**
	 * @param index
	 *            the index of a decision
	 * @return true if the specified index corresponds to the first or second watch
	 */
	public boolean isWatch(int index) {
		return watch1 == index || watch2 == index;
	}

	/**
	 * @param decision
	 *            a decision
	 * @return true if the specified decision corresponds to the first or second watched decision
	 */
	public boolean isDecisionWatched(int decision) {
		return decisions[watch1] == decision || decisions[watch2] == decision;
	}

	/**
	 * @param watchedDecision
	 *            a watched decision
	 * @return the watched decision which is not the specified one
	 */
	public int watchedDecisionOtherThan(int watchedDecision) {
		assert isDecisionWatched(watchedDecision);
		return decisions[watch1] == watchedDecision ? decisions[watch2] : decisions[watch1];
	}

	/**
	 * Builds a nogood from the specified (negative) decision)
	 * 
	 * @param negativeDecisions
	 *            the negative decisions forming the nogood
	 */
	public Nogood(int[] negativeDecisions) {
		control(negativeDecisions.length > 1 && Arrays.stream(negativeDecisions).noneMatch(d -> d >= 0));
		this.decisions = negativeDecisions;
		this.watch1 = 0;
		this.watch2 = negativeDecisions.length - 1;
	}

	public String toString(Decisions sdecisions) {
		return IntStream.of(decisions).mapToObj(d -> sdecisions.stringOf(d)).collect(Collectors.joining(" "));
	}

}
