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

import java.util.Arrays;
import java.util.stream.Stream;

import constraints.global.AllDifferent.AllDifferentComplete;
import problem.Problem;
import sets.SetSparse;
import variables.Variable;

/**
 * The constraint Circuit ensures that the values taken by a sequence of variables <x0,x1, ...> forms a circuit, with
 * the assumption that each pair (i,xi) represents an arc. See for example "Introducing global constraints in CHIP",
 * Mathematical and Computer Modelling, 20(12):97–123, 1994 by N. Beldiceanu and E. Contejean.
 * 
 * @author Christophe Lecoutre
 */
public final class Circuit extends AllDifferentComplete {

	@Override
	public boolean isSatisfiedBy(int[] t) {
		if (super.isSatisfiedBy(t) == false)
			return false;
		int nLoops = 0, first = -1;
		for (int i = 0; i < t.length; i++)
			if (t[i] == i)
				nLoops++;
			else if (first == -1)
				first = i;
		if (nLoops == t.length)
			return false; // because no circuit at all
		Arrays.fill(tmp, false);
		int i = first, size = 0;
		while (!tmp[t[i]]) {
			if (t[i] == i)
				return false; // because badly formed circuit
			tmp[t[i]] = true;
			i = t[i];
			size++;
		}
		return size == t.length - nLoops;
	}

	/**
	 * A sparse set used during filtering
	 */
	private final SetSparse set;

	/**
	 * A temporary array
	 */
	private final boolean[] tmp;

	/**
	 * Build a constraint Circuit for the specified problem over the specified array of variables
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public Circuit(Problem pb, Variable[] scp) {
		super(pb, scp);
		this.set = new SetSparse(scp.length);
		this.tmp = new boolean[scp.length];
		control(Stream.of(scp).allMatch(x -> 0 <= x.dom.firstValue() && x.dom.lastValue() < scp.length));
	}

	@Override
	public boolean isGuaranteedAC() {
		return false;
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (super.runPropagator(x) == false)
			return false;
		if (futvars.size() == 0)
			return true;
		int minimalCircuitLength = 0;
		for (int i = 0; i < scp.length; i++)
			if (doms[i].containsValue(i) == false)
				minimalCircuitLength++;
		Arrays.fill(tmp, false);
		for (int i = 0; i < scp.length; i++) {
			if (doms[i].size() > 1 || tmp[i])
				continue;
			int j = doms[i].singleValue();
			if (i == j)
				continue; // because self-loop
			set.clear();
			set.add(i); // i belongs to the circuit
			if (doms[j].removeValueIfPresent(j) == false) // because self-loop not possible for j
				return false;
			while (set.size() + 1 < minimalCircuitLength) {
				if (doms[j].removeValuesIn(set) == false)
					return false; // because we cannot close the circuit now (it would be too short)
				if (doms[j].size() > 1)
					break;
				tmp[j] = true;
				if (set.contains(j))
					return false; // because two times the same value (and too short circuit)
				set.add(j); // j belongs to the circuit
				j = doms[j].singleValue(); // we know that the *new value of j* is different from the previous one
				if (doms[j].removeValueIfPresent(j) == false) // because self-loop not possible for j
					return false;
			}
			if (doms[j].size() == 1 && doms[j].singleValue() == set.dense[0]) {
				// System.out.println("closed circuit " + (set.size() + 1));
				// for (int l = 0; l < set.limit; l++) System.out.println(l + ": " + set.dense[l]);
				// System.out.println(" plus " + j + " " + doms[j].singleValue());
				for (int k = 0; k < scp.length; k++)
					if (j != k && !set.contains(k) && doms[k].reduceToValue(k) == false)
						return false;
				return entailed();
			}
		}
		return true;
	}

}
