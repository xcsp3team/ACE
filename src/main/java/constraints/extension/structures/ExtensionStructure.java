/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension.structures;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import constraints.Constraint;
import constraints.ConstraintExtension;
import interfaces.ConstraintRegister;
import utility.Kit;
import utility.Kit.IntArrayHashKey;
import variables.Domain;
import variables.Variable;

/**
 * This is the root class for representing the structures to be used with extension (table) constraints. For example,
 * this can be a matrix (if the constraint is binary), a trie or an MDD.
 * 
 * @author Christophe Lecoutre
 */
public abstract class ExtensionStructure implements ConstraintRegister {

	/**
	 * The tuples as given initially, before being possibly converted into a specific structure like, e.g., an MDD
	 */
	public int[][] originalTuples;

	/**
	 * The Boolean as given initially for stating if the original tuples are supports or conflicts
	 */
	public boolean originalPositive;

	/**
	 * The list of constraints that have been registered with the structure
	 */
	private final List<Constraint> registeredCtrs = new ArrayList<>();

	@Override
	public List<Constraint> registeredCtrs() {
		return registeredCtrs;
	}

	/**
	 * Builds an extension structure to be used with the specified extension constraint
	 * 
	 * @param c
	 *            an extension constraint to which the structure is attached
	 */
	public ExtensionStructure(ConstraintExtension c) {
		registeredCtrs.add(c);
	}

	/**
	 * Records the tuples defining the semantics of the extension constraint. The structure is built adequately, for
	 * example under the form of a matrix, a trie or an MDD.
	 * 
	 * @param tuples
	 *            the tuples defining the semantics of the extension constraint
	 * @param positive
	 *            indicates if the tuples are supports or conflicts
	 */
	public abstract void storeTuples(int[][] tuples, boolean positive);

	/**
	 * Determines if the specified tuple corresponds to a support of the extension constraint, i.e., if the tuple of
	 * values corresponding to the indexes in the specified tuple satisfies the constraint. Be careful: the given tuple
	 * must contains indexes of values.
	 * 
	 * @param t
	 *            a tuple of indexes (of values)
	 * @return true if the tuple of values corresponding to the specified tuple of indexes satisfies the extension
	 *         constraint
	 */
	public abstract boolean checkIndexes(int[] t);

	/**
	 * Returns the first support for (x,a) that can be found from the specified tuple (included in the search), or null.
	 * This method is currently only used by ExtensionVA.
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            an index (of value) for the variable
	 * @param the
	 *            tuple from which starting the search
	 * @return the first support that can be found for (x,a) from the specified tuple (included in the search), or null
	 */
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

	/**
	 * Returns the array of symmetry colors for the specified extension constraint
	 * 
	 * @param c
	 *            a constraint
	 * @return the array of symmetry colors for the specified constraint
	 */
	public int[] computeVariableSymmetryMatching(ConstraintExtension c) {
		// TODO not sure we could use a cache (or we must be careful about the type of the variable domains)
		assert registeredCtrs.stream().anyMatch(cc -> cc == c);
		Variable[] scp = c.scp;
		if (scp.length == 1)
			return new int[] { 1 };
		if (!Variable.haveSameDomainType(scp))
			return Kit.series(1, scp.length); // TODO there exists a possibility of finding symmetry of variables (but
												// not a single group)
		if (scp.length == 2) {
			Domain dom0 = scp[0].dom, dom1 = scp[1].dom;
			int[] t = c.tupleIterator.buffer;
			for (int[] tuple : originalTuples) {
				t[0] = dom0.toIdx(tuple[1]);
				t[1] = dom1.toIdx(tuple[0]);
				if (checkIndexes(t) != originalPositive)
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

	/**
	 * Removes the tuple of the extension structure. This operation can only performed for some specific structures, and
	 * is used with second-order consistencies such as path-consistency or dual-consisteny. Note that the tuple contains
	 * index of values (and not values)
	 * 
	 * @param t
	 *            a tuple of indexes (of values)
	 * @return true if the tuple has been removed (if it was already absent, false is returned)
	 */
	public boolean removeTuple(int[] t) {
		throw new AssertionError("relevant only for some subclasses when 2nd order consistencies are used");
	}

	/**
	 * Increments the counter of removed tuples
	 */
	protected final void incrementNbTuplesRemoved() {
		firstRegisteredCtr().problem.solver.propagation.nTuplesRemoved++;
	}
}