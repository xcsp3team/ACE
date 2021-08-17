/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension.structures;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import constraints.Constraint;
import constraints.Constraint.RegisteringCtrs;
import utility.Kit;
import utility.Kit.IntArrayHashKey;
import variables.Domain;
import variables.Variable;

public abstract class ExtensionStructure implements RegisteringCtrs {

	public final List<Constraint> registeredCtrs = new ArrayList<>();

	@Override
	public List<Constraint> registeredCtrs() {
		return registeredCtrs;
	}

	public ExtensionStructure(Constraint c) {
		registeredCtrs.add(c);
	}

	/**
	 * We assume that the given array corresponds to a tuple of indexes (and not to a tuple of values).
	 */
	public boolean removeTuple(int[] tupleToBeRemoved) {
		throw new AssertionError("relevant only for some subclasses when 2nd order consistencies are used");
	}

	protected final void incrementNbTuplesRemoved() {
		firstRegisteredCtr().problem.solver.propagation.nTuplesRemoved++;
	}

	public String[][] symbolicTuples; // in case of a symbolic table constraint

	public int[][] originalTuples;

	public boolean originalPositive;

	public abstract void storeTuples(int[][] tuples, boolean positive);

	public abstract boolean checkIdxs(int[] t);

	public int[] nextSupport(int x, int a, int[] current) {
		throw new UnsupportedOperationException();
	}

	private boolean areSymmetricPositions(Set<IntArrayHashKey> set, int[][] tuples, int i, int j) {
		IntArrayHashKey key = new IntArrayHashKey();
		for (int[] tuple : tuples) {
			key.t = Kit.swap(tuple, i, j);
			boolean b = set.contains(key);
			Kit.swap(tuple, i, j);
			if (!b)
				return false;
		}
		return true;
	}

	public int[] computeVariableSymmetryMatching(Constraint c) { // TODO not sure we could use a cache (or we must be careful about the type of the variable
																	// domains)
		assert registeredCtrs.stream().anyMatch(cc -> cc == c);
		Variable[] scp = c.scp;
		if (scp.length == 1)
			return new int[] { 1 };
		if (!Variable.haveSameDomainType(scp))
			return Kit.range(1, scp.length); // TODO there exists a possibility of finding symmetry of variables (but not a single group)
		if (scp.length == 2) {
			Domain dom0 = scp[0].dom, dom1 = scp[1].dom;
			int[] t = c.tupleIterator.buffer;
			for (int[] tuple : originalTuples) {
				t[0] = dom0.toIdx(tuple[1]);
				t[1] = dom1.toIdx(tuple[0]);
				if (checkIdxs(t) != originalPositive)
					return new int[] { 1, 2 };
			}
			return new int[] { 1, 1 };
		}
		Set<IntArrayHashKey> set = new HashSet<>();
		for (int[] t : originalTuples)
			set.add(new IntArrayHashKey(t));
		int[] permutation = new int[scp.length];
		int color = 1;
		for (int i = 0; i < permutation.length; i++)
			if (permutation[i] == 0) {
				for (int j = i + 1; j < permutation.length; j++)
					if (permutation[j] == 0 && areSymmetricPositions(set, originalTuples, i, j))
						permutation[j] = color;
				permutation[i] = color++;
			}
		return permutation;
	}
}