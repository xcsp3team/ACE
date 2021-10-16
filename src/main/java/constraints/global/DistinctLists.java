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

import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import constraints.ConstraintGlobal;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotSymmetric;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * A constraint that ensures that two lists/vectors of variables (of same size) are not equal, i.e., do not form the
 * same tuple of values. IMPORTANT: for the moment, when the same variable occurs several times, AC is not guaranteed.
 * We find 279360 solutions for: <br />
 * java ace Crossword-ogd-p02.xml -s=all -varh=Dom -g_dv=1 // intension <br />
 * java ace Crossword-ogd-p02.xml -s=all -varh=Dom -g_dv=1 -hybrid // smart tables <br />
 * java ace Crossword-ogd-p02.xml -s=all -varh=Dom // distinct lists
 * 
 * @author Christophe Lecoutre
 */
public final class DistinctLists extends ConstraintGlobal implements TagCallCompleteFiltering, TagNotSymmetric, ObserverOnBacktracksSystematic {

	@Override
	public boolean isSatisfiedBy(int[] t) {
		for (int i = 0; i < half; i++)
			if (t[pos1[i]] != t[pos2[i]])
				return true;
		return false;
	}

	@Override
	public void restoreBefore(int depth) {
		if (uniqueSentinelLevel == depth)
			uniqueSentinelLevel = -1;
	}

	@Override
	public boolean isGuaranteedAC() {
		return scp.length == 2 * half; // AC is guaranteed if not several occurrences of the same variable
	}

	/**
	 * A first list (actually array) of variables
	 */
	private final Variable[] list1;

	/**
	 * A second list (actually array) of variables
	 */
	private final Variable[] list2;

	/**
	 * pos1[i] is the position of the variable list1[i] in the constraint scope
	 */
	private final int[] pos1;

	/**
	 * pos2[i] is the position of the variable list2[i] in the constraint scope
	 */
	private final int[] pos2;

	/**
	 * The size of the lists (half of the scope size)
	 */
	private final int half;

	/**
	 * Initial mode: two sentinels for tracking the presence of different values.
	 */
	private int sentinel1, sentinel2;

	/**
	 * Possible mode: only one remaining sentinel, identified at a certain level
	 */
	private int uniqueSentinel, uniqueSentinelLevel = -1;

	/**
	 * Build a constraint DistinctLists for the specified problem over the two specified lists of variables
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param list1
	 *            a first list of variables
	 * @param list2
	 *            a second list of variables
	 */
	public DistinctLists(Problem pb, Variable[] list1, Variable[] list2) {
		super(pb, pb.vars(list1, list2));
		this.half = list1.length;
		this.list1 = list1;
		this.list2 = list2;
		control(1 < half && half == list2.length && IntStream.range(0, half).allMatch(i -> list1[i] != list2[i]));
		this.pos1 = IntStream.range(0, half).map(i -> Utilities.indexOf(list1[i], scp)).toArray();
		this.pos2 = IntStream.range(0, half).map(i -> Utilities.indexOf(list2[i], scp)).toArray();
		this.sentinel1 = 0;
		this.sentinel2 = half - 1;
	}

	private boolean handleUniqueSentinel(Domain dom1, Domain dom2) {
		if (dom1.size() > 1 && dom2.size() > 1)
			return true;
		if (dom1.size() == 1)
			return dom2.removeValueIfPresent(dom1.singleValue()) && entailed();
		return dom1.removeValueIfPresent(dom2.singleValue()) && entailed();
	}

	private boolean isGoodSentinel(Domain dom1, Domain dom2) {
		return dom1.size() > 1 || dom2.size() > 1 || dom1.singleValue() != dom2.singleValue();
	}

	private int findAnotherSentinel() {
		for (int i = 0; i < half; i++)
			if (i != sentinel1 && i != sentinel2 && isGoodSentinel(list1[i].dom, list2[i].dom))
				return i;
		return -1;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		if (uniqueSentinelLevel != -1)
			return handleUniqueSentinel(list1[uniqueSentinel].dom, list2[uniqueSentinel].dom);

		Domain dx1 = list1[sentinel1].dom, dx2 = list2[sentinel1].dom, dy1 = list1[sentinel2].dom, dy2 = list2[sentinel2].dom;
		if (dx1.size() == 1 && dx2.size() == 1) { // possibly, sentinel1 is no more valid
			if (dx1.singleValue() != dx2.singleValue())
				return entailed();
			int sentinel = findAnotherSentinel();
			if (sentinel != -1) {
				sentinel1 = sentinel;
				dx1 = list1[sentinel1].dom;
				dx2 = list2[sentinel1].dom;
			} else {
				uniqueSentinel = sentinel2;
				uniqueSentinelLevel = problem.solver.depth();
				return handleUniqueSentinel(dy1, dy2);
			}
		}
		if (dy1.size() == 1 && dy2.size() == 1) { // possibly, sentinel2 is no more valid
			if (dy1.singleValue() != dy2.singleValue())
				return entailed();
			int sentinel = findAnotherSentinel();
			if (sentinel != -1) {
				sentinel2 = sentinel;
			} else {
				uniqueSentinel = sentinel1;
				uniqueSentinelLevel = problem.solver.depth();
				return handleUniqueSentinel(dx1, dx2);
			}
		}
		return true;
	}
}
