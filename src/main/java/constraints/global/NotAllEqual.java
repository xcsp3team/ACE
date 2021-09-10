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
import variables.Domain;
import variables.Variable;

/**
 * This constraint ensures that all values assigned to the variables of its scope are not all equal. It is a special case of a counting constraint.
 * 
 * @author Christophe Lecoutre
 */
public class NotAllEqual extends ConstraintGlobal implements TagSymmetric, TagAC, TagCallCompleteFiltering {

	@Override
	public final boolean isSatisfiedBy(int[] t) {
		for (int i = 0; i < t.length - 1; i++)
			if (t[i] != t[i + 1])
				return true;
		return false;
	}

	/**
	 * Build a constraint NotAllEqual for the specified problem over the specified array/list of variables
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param list
	 *            the involved variables
	 */
	public NotAllEqual(Problem pb, Variable[] list) {
		super(pb, list);
		control(list.length > 2);
		defineKey();
	}

	@Override
	public boolean runPropagator(Variable evt) {
		Variable unfixed = null;
		int uniqueFixedVal = Integer.MAX_VALUE; // this value cannot be present in integer domains
		// iteration over future variables first
		for (int i = futvars.limit; i >= 0; i--) {
			Domain dom = scp[futvars.dense[i]].dom;
			if (dom.size() > 1) {
				if (unfixed == null)
					unfixed = dom.var();
				else
					return true; // AC because at least two unfixed variables
			} else {
				if (uniqueFixedVal == Integer.MAX_VALUE)
					uniqueFixedVal = dom.singleValue();
				else if (uniqueFixedVal != dom.singleValue())
					return entailed(); // entailed because two fixed variables with different values
			}
		}
		// iteration over past variable then
		for (int i = futvars.size(); i < scp.length; i++) {
			Domain dom = scp[futvars.dense[i]].dom;
			if (uniqueFixedVal == Integer.MAX_VALUE)
				uniqueFixedVal = dom.singleValue();
			else if (uniqueFixedVal != dom.singleValue())
				return entailed();
		}
		if (unfixed == null)
			return evt.dom.fail(); // because all variables are assigned to the same value
		assert uniqueFixedVal != Integer.MAX_VALUE;
		return unfixed.dom.removeValueIfPresent(uniqueFixedVal) && entailed();
	}
}
