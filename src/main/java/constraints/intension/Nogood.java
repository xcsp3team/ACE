/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.intension;

import static utility.Kit.control;

import java.util.stream.IntStream;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * This constraint ensures that at least one variable take a value different form the one associated with it.
 * 
 * @author Christophe Lecoutre
 */
public class Nogood extends ConstraintGlobal implements TagAC, TagCallCompleteFiltering {

	@Override
	public boolean isSatisfiedBy(int[] tuple) {
		for (int i = 0; i < vars.length; i++)
			if (tuple[i] != vals[i])
				return true;
		return false;
	}

	private Variable[] vars;

	private int[] vals;

	/** Two sentinels for tracking the presence of two possibly satisfying assignments. */
	private int sentinel1, sentinel2;

	public Nogood(Problem pb, Variable[] vars, int[] vals) {
		super(pb, vars);
		this.vars = vars;
		this.vals = vals;
		control(vars.length > 1 && vars.length == vals.length, () -> "" + vars.length);
		control(IntStream.range(0, vars.length).allMatch(i -> vars[i].dom.size() > 1 && vars[i].dom.containsValue(vals[i])));
		sentinel1 = 0;
		sentinel2 = 1;
	}

	private int findAnotherSentinel() {
		for (int i = 0; i < vars.length; i++) {
			if (i == sentinel1 || i == sentinel2)
				continue;
			if (vars[i].dom.containsValue(vals[i]) == false)
				return Integer.MAX_VALUE;
			else if (vars[i].dom.size() > 1)
				return i;
		}
		return -1;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		if (vars[sentinel1].dom.containsValue(vals[sentinel1]) == false)
			return entail();
		if (vars[sentinel1].dom.size() == 1) {
			int sentinel = findAnotherSentinel();
			if (sentinel == Integer.MAX_VALUE)
				return entail();
			if (sentinel == -1) {
				Domain dom = vars[sentinel2].dom;
				if (dom.containsValue(vals[sentinel2]) && dom.removeValue(vals[sentinel2]) == false)
					return dom.fail();
				return entail();
			} else
				sentinel1 = sentinel;
		}
		if (vars[sentinel2].dom.containsValue(vals[sentinel2]) == false)
			return entail();
		if (vars[sentinel2].dom.size() == 1) {
			int sentinel = findAnotherSentinel();
			if (sentinel == Integer.MAX_VALUE)
				return entail();
			if (sentinel == -1) {
				Domain dom = vars[sentinel1].dom;
				if (dom.containsValue(vals[sentinel1]) && dom.removeValue(vals[sentinel1]) == false)
					return dom.fail();
				return entail();
			} else
				sentinel2 = sentinel;
		}
		return true;
	}
}