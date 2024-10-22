/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import static utility.Kit.control;

import constraints.ConstraintGlobal;
import constraints.global.Matcher.MatcherCardinality;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagPostponableFiltering;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import propagation.StrongConsistency;
import utility.Kit;
import variables.Variable;

/**
 * This constraint Cardinality ensures that the number of occurrences of some values respect some conditions.
 * 
 * @author Christophe Lecoutre and Vincent Perradin
 */
public final class Cardinality extends ConstraintGlobal
		implements TagAC, TagCallCompleteFiltering, TagPostponableFiltering, TagSymmetric, ObserverOnBacktracksSystematic {

	@Override
	public void restoreBefore(int depth) {
		matcher.restoreAtDepthBefore(depth);
	}

	@Override
	public boolean isSatisfiedBy(int[] t) {
		for (int i = 0; i < values.length; i++) {
			int nOccurrences = 0;
			for (int j = 0; j < t.length; j++)
				if (t[j] == values[i])
					nOccurrences++;
			if (nOccurrences < minOccs[i] || nOccurrences > maxOccs[i])
				return false;
		}
		return true;
	}

	/**
	 * The values that must be counted
	 */
	private final int[] values;

	/**
	 * minOccs[i] is the required minimal number of occurrences of the value values[i]
	 */
	private final int[] minOccs;

	/**
	 * maxOccs[i] is the required maximal number of occurrences of the value values[i]
	 */
	private final int[] maxOccs;

	/**
	 * The object used to compute a maximal matching, and to delete inconsistent values
	 */
	protected Matcher matcher;

	/**
	 * Builds a constraint Cardinality for the specified problem
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 * @param values
	 *            the values that must be counted
	 * @param minOccs
	 *            the minimal number of occurrences of each value
	 * @param maxOccs
	 *            the maximal number of occurrences of each value
	 */
	public Cardinality(Problem pb, Variable[] scp, int[] values, int[] minOccs, int[] maxOccs) {
		super(pb, scp);
		control(scp.length > 1 && values.length == minOccs.length && values.length == maxOccs.length);
		this.values = values;
		this.minOccs = minOccs;
		this.maxOccs = maxOccs;
		this.matcher = new MatcherCardinality(this, values, minOccs, maxOccs);
		defineKey(values, minOccs, maxOccs);
	}

	/**
	 * Builds a constraint Cardinality for the specified problem
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 * @param values
	 *            the values that must be counted
	 * @param nOccs
	 *            the exact number of occurrences for each value
	 */
	public Cardinality(Problem pb, Variable[] scp, int[] values, int[] nOccs) {
		this(pb, scp, values, nOccs, nOccs);
	}

	/**
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the problem to which the constraint is attached
	 * @param values
	 *            the values that must be counted
	 * @param minOccs
	 *            the minimal number of occurrences for each value
	 * @param maxOccs
	 *            the maximal number of occurrences for each value
	 */
	public Cardinality(Problem pb, Variable[] scp, int[] values, int minOccs, int maxOccs) {
		this(pb, scp, values, Kit.repeat(minOccs, values.length), Kit.repeat(maxOccs, values.length));
	}

	long lastSafeNumber = -1;

	@Override
	public boolean runPropagator(Variable x) {
		// System.out.println("running " + x + " at level " + problem.solver.depth());
		if (!matcher.findMaximumMatching())
			return x.dom.fail();
		matcher.removeInconsistentValues();

		return true;
	}

}
