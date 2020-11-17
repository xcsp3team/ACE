/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.structures.forSac;

import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import search.Solver;
import variables.Variable;

public class Branch {
	protected final Solver solver;

	public final Variable[] vars;

	public final int[] idxs;

	protected final int[] positions;

	public int size;

	public Branch(Solver solver) {
		this.solver = solver;
		this.vars = new Variable[solver.pb.variables.length];
		this.idxs = new int[solver.pb.variables.length];
		this.positions = new int[solver.pb.variables.length];
	}

	public void clear() {
		size = 0;
		Arrays.fill(positions, -1);
	}

	public boolean has(Variable x) {
		return positions[x.num] != -1;
	}

	public void add(Variable x, int a) {
		assert !has(x);
		vars[size] = x;
		idxs[size] = a;
		positions[x.num] = size;
		size++;
		assert IntStream.of(positions).filter(v -> v != -1).count() == size;
	}

	public boolean controlWrt(QueueOfCells queue) {
		for (int i = 0; i < size; i++) {
			if (queue.isPresent(vars[i], idxs[i]))
				return false;
			// if (!vars[i].dom.hasIndex(idxs[i]))
			// return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return "Branch : " + IntStream.range(0, size).mapToObj(i -> (vars[i] + "<-" + idxs[i])).collect(Collectors.joining(" "));
	}
}