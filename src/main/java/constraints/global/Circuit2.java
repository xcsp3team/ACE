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
 * The constraint circuit ensures that the values taken by a sequence of variables <x0,x1, ...> forms a circuit, with
 * the assumption that each pair (i,xi) represents an arc. See for example "Introducing global constraints in CHIP",
 * Mathematical and Computer Modelling, 20(12):97–123, 1994 by N. Beldiceanu and E. Contejean.
 * 
 * @author Christophe Lecoutre
 * 
 */
public final class Circuit2 extends AllDifferentComplete {

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

	private final SetSparse heads;

	private final SetSparse pheads;

	/**
	 * A sparse set used during filtering
	 */
	private final SetSparse set;

	/**
	 * A temporary array
	 */
	private final boolean[] tmp;

	private final boolean[] pred;

	/**
	 * Build a constraint Circuit for the specified problem over the specified array/list of variables
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param list
	 *            the involved variables
	 */
	public Circuit2(Problem pb, Variable[] list) {
		super(pb, list);
		this.set = new SetSparse(list.length);
		this.tmp = new boolean[list.length];
		this.pred = new boolean[list.length];
		control(Stream.of(list).allMatch(x -> 0 <= x.dom.firstValue() && x.dom.lastValue() < list.length));

		this.heads = new SetSparse(list.length);
		this.pheads = new SetSparse(list.length);
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
		// for (int i = 0; i < scp.length; i++)
		// if (doms[i].containsValue(i) == false)
		// minimalCircuitLength++;

		heads.clear();
		int circuitNode = -1;
		pheads.fill();
		int nArcs = 0;
		Arrays.fill(pred, false);
		for (int i = 0; i < scp.length; i++) {
			if (doms[i].containsValue(i) == false)
				minimalCircuitLength++;
			if (doms[i].size() == 1) {
				// if (pheads.contains(i)) pheads.remove(i);
				int j = doms[i].singleValue();
				if (i == j)
					continue; // because auto-loop
				nArcs++;
				// if (pheads.contains(j)) pheads.remove(j);
				if (pred[i] == false)
					heads.add(i);
				if (pred[j] == true)
					return false; // fail because two predecessors
				pred[j] = true;
				if (heads.contains(j)) {
					heads.remove(j);
					if (heads.isEmpty()) // it means that we have a closed circuit
						circuitNode = i;
				}
			}
		}
		if (circuitNode != -1) {
			if (!heads.isEmpty())
				return false; // because a closed circuit and a separate chain
			set.clear();
			int i = circuitNode;
			set.add(i);
			while (true) {
				i = doms[i].singleValue();
				if (i == circuitNode)
					break;
				set.add(i);
			}
			if (set.size() < nArcs)
				return false;
			for (int k = 0; k < scp.length; k++)
				if (!set.contains(k) && doms[k].reduceToValue(k) == false)
					return false;
			return entailed();
		}
		int cnt = 0;
		Arrays.fill(tmp, false);
		for (int p = heads.limit; p >= 0; p--) {
			int i = heads.dense[p];
			if (tmp[i])
				continue; // because it is a head that has just been reached from another head after filtering
			control(doms[i].size() == 1 && doms[i].singleValue() != i);
			int j = doms[i].singleValue();
			int head = i;
			set.clear();
			// set.add(i); // i belongs to the circuit
			while (true) {
				int before = doms[j].size();
				if (set.contains(j))
					return false; // because two times the same value (and too short circuit)
				if (doms[j].removeValueIfPresent(j) == false) // because self-loop not possible for j
					return false;
				if (set.size() + 2 < minimalCircuitLength)
					if (doms[j].removeValueIfPresent(head) == false)
						return false;
				if (doms[j].removeValuesIn(set) == false)
					return false; // because we cannot close the circuit now (it would be too short)
				if (pred[j])
					cnt++;
				if (doms[j].size() > 1)
					break;
				set.add(j); // j belongs to the circuit
				j = doms[j].singleValue(); // we know that the *new value of j* is different from the previous one
				if (before > 1) {
					// if (pheads.contains(j)) pheads.remove(j);
					if (heads.contains(j))
						tmp[j] = true;
				}
				if (j == head) { // closed circuit
					for (int k = 0; k < scp.length; k++)
						if (k != head && !set.contains(k) && doms[k].reduceToValue(k) == false)
							return false;
					return entailed();
				}
			}
		}
		if (cnt < nArcs)
			return false;

		return true;
	}

}
