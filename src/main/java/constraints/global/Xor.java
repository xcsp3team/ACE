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
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import variables.Variable;

/**
 * The constraint Xor ensures that there is an odd number of variables assigned to 1.
 * 
 * @author Christophe Lecoutre
 */
public final class Xor extends ConstraintGlobal implements TagAC, TagCallCompleteFiltering, TagSymmetric {

	@Override
	public boolean isSatisfiedBy(int[] t) {
		int cnt = 0;
		for (int v : t)
			if (v == 1)
				cnt++;
		return cnt % 2 == 1;
	}

	private Variable sentinel1, sentinel2;

	/**
	 * Builds a constraint Xor for the specified problem
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param list
	 *            the list of variables where we have to count the number of 1
	 */
	public Xor(Problem pb, Variable[] list) {
		super(pb, list);
		control(list.length >= 2 && Variable.areAllInitiallyBoolean(list));
		this.sentinel1 = scp[0];
		this.sentinel2 = scp[scp.length - 1];
	}

	private Variable findAnotherSentinel() {
		for (Variable x : scp)
			if (x != sentinel1 && x != sentinel2 && x.dom.size() > 1)
				return x;
		return null;
	}

	private boolean enforceSentinel(Variable sentinel) {
		int cnt = 0;
		for (Variable x : scp)
			if (x != sentinel && x.dom.single() == 1)
				cnt++;
		return sentinel.dom.reduceTo(cnt % 2 == 0 ? 1 : 0) && entail();
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (sentinel1.dom.size() == 1) {
			Variable y = findAnotherSentinel();
			if (y == null)
				return enforceSentinel(sentinel2);
			sentinel1 = y;
		}
		if (sentinel2.dom.size() == 1) {
			Variable y = findAnotherSentinel();
			if (y == null)
				return enforceSentinel(sentinel1);
			sentinel2 = y;
		}
		return true;
	}

}
