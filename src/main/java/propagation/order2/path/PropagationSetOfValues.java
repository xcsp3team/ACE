/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order2.path;

import java.util.Arrays;

import constraints.Constraint;
import constraints.CtrHard;
import problem.Problem;
import variables.Variable;

public class PropagationSetOfValues {
	private int positions[][][];

	private int capacity;

	private int size;

	private final CtrHard[] ctrs;

	private final Variable[] vars;

	private final int[] idxs;

	private int head;

	public CtrHard firstConstraint() {
		return ctrs[head];
	}

	public Variable firstVariable() {
		return vars[head];
	}

	public int firstIndex() {
		return idxs[head];
	}

	// by the way, if necessary the last element can be accessed with (head + nbCurrentValues - 1) % capacity

	public PropagationSetOfValues(Problem problem) {
		capacity = 0;
		positions = new int[problem.constraints.length][][];
		for (int i = 0; i < positions.length; i++) {
			Constraint c = problem.constraints[i];
			if (c.scp.length != 2)
				continue;
			positions[i] = new int[2][];
			for (int j = 0; j < positions[i].length; j++) {
				positions[i][j] = new int[c.scp[j].dom.initSize()];
				Arrays.fill(positions[i][j], -1);
				capacity += c.scp[j].dom.initSize();
			}
		}
		ctrs = new CtrHard[capacity];
		vars = new Variable[capacity];
		idxs = new int[capacity];
	}

	public PropagationSetOfValues add(CtrHard c, Variable x, int a) {
		int p = c.positionOf(x);
		if (positions[c.num][p][a] != -1)
			return this;
		int firstFreePosition = (head + size) % capacity;
		positions[c.num][p][a] = firstFreePosition;
		ctrs[firstFreePosition] = c;
		vars[firstFreePosition] = x;
		idxs[firstFreePosition] = a;
		size++;
		return this;
	}

	public void remove(int i) {
		assert i >= 0 && i < size; // head && i <= (head + nbCurrentValues - 1) % capacity;
		int position = (head + i) % capacity;
		positions[ctrs[position].num][ctrs[position].positionOf(vars[position])][idxs[position]] = -1;
		if (position == head)
			head = (head + 1) % capacity;
		else {
			int lastPosition = (head + size - 1) % capacity;
			if (position != lastPosition) {
				ctrs[position] = ctrs[lastPosition];
				vars[position] = vars[lastPosition];
				idxs[position] = idxs[lastPosition];
				positions[ctrs[position].num][ctrs[position].positionOf(vars[position])][idxs[position]] = position;
			}
		}
		size--;
	}

	public int size() {
		return size;
	}
}