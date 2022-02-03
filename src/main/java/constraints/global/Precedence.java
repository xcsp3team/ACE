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

import org.xcsp.common.Utilities;

import constraints.ConstraintGlobal;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import problem.Problem;
import variables.Variable;

/**
 * The constraint Precedence is defined over a sequence v of k values, and imposes over a sequence x of variables (the
 * scope) for any i in 1..k-1 that if there exists j such that x[j] = v[i], then there must exist j' < j such that x[j']
 * = v[i-1].
 * 
 * @author Christophe Lecoutre
 */
public final class Precedence extends ConstraintGlobal implements TagNotAC, TagCallCompleteFiltering, ObserverOnBacktracksSystematic {
	// TODO: replace size by left and right to reason from both sides

	@Override
	public boolean isSatisfiedBy(int[] t) {
		int i = 0, prev = Utilities.indexOf(values[0], t);
		while (i < k - 1 && prev != -1) {
			i++;
			int curr = Utilities.indexOf(values[i], t);
			if (curr != -1 && curr < prev)
				return false;
			prev = curr;
		}
		if (prev == -1) {
			if (covered)
				return false;
			// we check that all other values are absent
			for (int j = i + 1; j < k; j++)
				if (Utilities.indexOf(values[j], t) != -1)
					return false;
			return true;
		}
		return true;
	}

	@Override
	public void restoreBefore(int depth) {
		reinit = true;
	}

	/**
	 * The arity of the constraint
	 */
	private final int r;

	/**
	 * The number of involved values
	 */
	private final int k;

	private int[] values;

	private boolean covered;

	/**
	 * The number of values that still must be considered (those at indexes ranging from 0 to size-1) because of
	 * possibly assigned values
	 */
	private int size;

	private boolean reinit = true;

	private int[] firsts;

	private int dist = 5; // if dist is r, do we have GAC?

	/**
	 * Builds a constraint Precedence for the specified problem
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param list
	 *            the list of variables where we have to find positions of values
	 * @param values
	 *            the values that must occur in this order
	 * @param covered
	 *            true if all values must be assigned
	 */
	public Precedence(Problem pb, Variable[] list, int[] values, boolean covered) {
		super(pb, list);
		control((!covered || list.length > values.length) && values.length > 1);
		this.r = scp.length;
		this.k = values.length;
		this.values = values;
		this.covered = covered;
		this.firsts = new int[k];
		defineKey(values, covered);
		for (int i = 1; i < k; i++)
			for (int j = 0; j < i; j++)
				scp[j].dom.removeValueAtConstructionTime(values[i]);
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (reinit)
			size = k;
		control(size > 1);
		for (int i = 0; i < size; i++) {
			int v = values[i];
			int j = reinit ? i : firsts[i]; // i because of the initial removals
			while (j < r) {
				if (scp[j].dom.containsValue(v)) {
					if (i == 0 || firsts[i - 1] < j)
						break; // because valid
					if (scp[j].dom.removeValue(v) == false)
						return false;
				}
				j++;
			}
			firsts[i] = j;
			if (j == r) {
				if (covered)
					return false;
				// we remove all subsequent values
				for (int k = i + 1; k < size; k++) {
					int w = values[k];
					for (int l = reinit ? k : firsts[k]; l < r; l++)
						if (scp[l].dom.removeValueIfPresent(w) == false)
							return false;
				}
				size = i;
			}
		}
		for (int i = size - 1; i > 0; i--) {
			assert scp[firsts[i]].dom.containsValue(values[i]) && firsts[i] > firsts[i - 1];
			if (scp[firsts[i]].dom.size() > 1 || scp[firsts[i - 1]].dom.size() == 1)
				continue;
			if (firsts[i] - firsts[i - 1] > dist)
				continue;
			boolean absent = true;
			for (int j = firsts[i - 1] + 1; absent && j < firsts[i]; j++)
				if (scp[j].dom.containsValue(values[i - 1]))
					absent = false;
			if (absent)
				if (scp[firsts[i - 1]].dom.reduceToValue(values[i - 1]) == false)
					return false;
		}
		int i = size - 1;
		while (i > 0 && scp[firsts[i]].dom.size() == 1 && scp[firsts[i - 1]].dom.size() == 1)
			i--;
		size = i + 1;
		if (size <= 1)
			return entailed();
		return true;
	}

}
