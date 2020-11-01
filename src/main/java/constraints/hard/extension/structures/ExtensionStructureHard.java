/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension.structures;

import java.util.HashSet;
import java.util.Set;

import constraints.Constraint;
import utility.Kit;
import utility.Kit.IntArrayHashKey;
import utility.exceptions.MissingImplementationException;
import variables.Variable;
import variables.domains.Domain;

public abstract class ExtensionStructureHard extends ExtensionStructure {

	public String[][] symbolicTuples; // in case of a symbolic table constraint

	public int[][] originalTuples;
	public boolean originalPositive;

	public ExtensionStructureHard(Constraint c) {
		super(c);
	}

	public abstract void storeTuples(int[][] tuples, boolean positive);

	public abstract boolean checkIdxs(int[] t);

	public int[] nextSupport(int vap, int a, int[] current) {
		throw new MissingImplementationException();
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

	public int[] computeVariableSymmetryMatching(int[][] tuples, boolean positive) {
		Kit.control(firstRegisteredCtr().pb.rs.cp.settingProblem.isSymmetryBreaking());
		Constraint ctr = firstRegisteredCtr();
		if (!Variable.haveSameDomainType(ctr.scp)) {
			return Kit.range(1, ctr.scp.length);
		}
		// TODO just above, there exists a possibility of finding symmetry of variables (but not a single group)
		if (ctr.scp.length == 1)
			return new int[] { 1 };
		if (ctr.scp.length == 2) {
			Domain dom0 = ctr.scp[0].dom, dom1 = ctr.scp[1].dom;
			int[] tmp = ctr.tupleManager.localTuple;
			for (int[] tuple : tuples) {
				tmp[0] = dom0.toIdx(tuple[1]);
				tmp[1] = dom1.toIdx(tuple[0]);
				if (checkIdxs(tmp) != positive)
					return new int[] { 1, 2 };
			}
			return new int[] { 1, 1 };
		}
		Set<IntArrayHashKey> set = new HashSet<>();
		for (int[] t : tuples)
			set.add(new IntArrayHashKey(t));
		int[] permutation = new int[ctr.scp.length];
		int color = 1;
		for (int i = 0; i < permutation.length; i++)
			if (permutation[i] == 0) {
				for (int j = i + 1; j < permutation.length; j++)
					if (permutation[j] == 0 && areSymmetricPositions(set, tuples, i, j))
						permutation[j] = color;
				permutation[i] = color++;
			}
		return permutation;
	}

	public int[] computeVariableSymmetryMatching() {
		return Kit.range(1, firstRegisteredCtr().scp.length);
	}

	public boolean isSimilarTo(ExtensionStructureHard ext) {
		if (originalPositive != ext.originalPositive || originalTuples.length != ext.originalTuples.length)
			return false;
		if (originalTuples == ext.originalTuples || originalTuples.length == 0) // control about arity must be made elsewhere
			return true;
		if (originalTuples.length > 10000) // hard coding ; limit for search
			return false;
		for (int a = originalTuples[0].length - 1, i = originalTuples.length - 1; i >= 0; i--)
			for (int j = a; j >= 0; j--)
				if (originalTuples[i][j] != ext.originalTuples[i][j])
					return false;
		return true;
	}
}