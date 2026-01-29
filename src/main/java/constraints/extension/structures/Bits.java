/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension.structures;

import static utility.Kit.control;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.ConstraintExtension;
import problem.Problem;
import utility.Bit;
import utility.Kit;
import utility.Kit.LongArrayHashKey;
import variables.Domain;
import variables.Variable;

/**
 * This is the class for extension structures represented by bits, i.e., when bit vectors are used to represent supports
 * and conflicts. Currently, this is only relevant for binary extension constraints.
 * 
 * @author Christophe Lecoutre
 */
public final class Bits extends ExtensionStructure {

	/**********************************************************************************************
	 * Static members
	 *********************************************************************************************/

	/**
	 * Map used to share longs (seen as parts of bit vectors) in order to save memory space
	 */
	public static final Map<LongArrayHashKey, long[]> map = Collections.synchronizedMap(new LinkedHashMap<LongArrayHashKey, long[]>(2000)); // hard coding

	private static LongArrayHashKey hashKey = new LongArrayHashKey();

	private static int saveSpace(long[][] sups) {
		int cnt = 0;
		for (int i = 0; i < sups.length; i++) {
			hashKey.t = sups[i];
			long[] t = null;
			synchronized (map) {
				t = map.get(hashKey);
			}
			if (t == null) {
				synchronized (map) {
					map.put(hashKey, sups[i]);
				}
				hashKey = new LongArrayHashKey();
			} else {
				sups[i] = t;
				cnt++;
			}
		}
		return cnt;
	}

	private static boolean saveSpace(Problem problem, long[][] sups0, long[][] sups1) {
		if (problem.head.control.problem.shareBits) {
			int nBefore = problem.features.nSharedBitVectors;
			problem.features.nSharedBitVectors += saveSpace(sups0);
			problem.features.nSharedBitVectors += saveSpace(sups1);
			return problem.features.nSharedBitVectors > nBefore;
		}
		return false;
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	@Override
	public final boolean checkIndexes(int[] t) {
		return (sups0[t[0]][t[1] / Long.SIZE] & Bit.ONE_LONG_BIT_TO_1[t[1] % Long.SIZE]) != 0;
	}

	/**
	 * sups0[a] is the vector of bits used to indicate which indexes (of values) support the index a for the fist
	 * variable; the vector of bits is composed of long (bit set to 1 when a support)
	 */
	private long[][] sups0;

	/**
	 * sups1[b] is the vector of bits used to indicate which indexes (of values) support the index b for the second
	 * variable; the vector of bits is composed of long (bit set to 1 when a support)
	 */
	private long[][] sups1;

	/**
	 * sups0Filtered[a] is the sequence of longs of the vector of bits, used for the index a of the first variable, that
	 * are relevant (i.e., different from 0)
	 */
	private int[][] sups0Filtered;

	/**
	 * sups1Filtered[b] is the sequence of longs of the vector of bits , used for the index b of the second variable,
	 * that are relevant (i.e., different from 0)
	 */
	private int[][] sups1Filtered;

	/**
	 * indicates if some longs are shared or not (for saving memory)
	 */
	private boolean sharing;

	/**
	 * Returns the vectors of bits for the variable whose position is specified
	 * 
	 * @param p
	 *            the position of the variable in the constraint scope
	 * @return the vectors of bits for the variable whose position is specified
	 */
	public long[][] sups(int p) {
		return p == 0 ? sups0 : sups1;
	}

	/**
	 * Returns the vectors of bits (filtered) for the variable whose position is specified
	 * 
	 * @param p
	 *            the position of the variable in the constraint scope
	 * @return the vectors of bits (filtered) for the variable whose position is specified
	 */
	public int[][] supsFiletered(int p) {
		return p == 0 ? sups0Filtered : sups1Filtered;
	}

	/**
	 * Builds the filtered sequences of bit vectors
	 */
	private void buildFilters() {
		this.sups0Filtered = Stream.of(sups0).map(t -> IntStream.range(0, t.length).filter(i -> t[i] != 0L).toArray()).toArray(int[][]::new);
		this.sups1Filtered = Stream.of(sups1).map(t -> IntStream.range(0, t.length).filter(i -> t[i] != 0L).toArray()).toArray(int[][]::new);
	}

	public Bits(ConstraintExtension c) {
		super(c);
		control(c.scp.length == 2);
	}

	public Bits(ConstraintExtension c, Bits bits) { // called by reflection when cloning structures
		this(c);
		this.sups0 = Stream.of(bits.sups0).map(t -> t.clone()).toArray(long[][]::new);
		this.sups1 = Stream.of(bits.sups1).map(t -> t.clone()).toArray(long[][]::new);
		buildFilters();
		this.sharing = bits.sharing;
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		Constraint c = firstRegisteredCtr();
		Domain dom0 = c.scp[0].dom, dom1 = c.scp[1].dom;
		this.sups0 = new long[dom0.initSize()][dom1.initSize() / Long.SIZE + (dom1.initSize() % Long.SIZE != 0 ? 1 : 0)];
		this.sups1 = new long[dom1.initSize()][dom0.initSize() / Long.SIZE + (dom0.initSize() % Long.SIZE != 0 ? 1 : 0)];
		// Now, we fill up bitSups0
		if (positive) {
			if (c.indexesMatchValues)
				for (int[] tuple : tuples)
					sups0[tuple[0]][tuple[1] / Long.SIZE] |= Bit.ONE_LONG_BIT_TO_1[tuple[1] % Long.SIZE];
			else
				for (int[] tuple : tuples) {
					int val0 = dom0.toIdx(tuple[0]), val1 = dom1.toIdx(tuple[1]);
					sups0[val0][val1 / Long.SIZE] |= Bit.ONE_LONG_BIT_TO_1[val1 % Long.SIZE];
				}
		} else {
			for (long[] t : sups0) {
				Arrays.fill(t, Bit.ALL_LONG_BITS_TO_1);
				int remainder = dom1.initSize() % Long.SIZE;
				if (remainder != 0)
					t[t.length - 1] = Bit.bitsAt1To(remainder);
			}
			if (c.indexesMatchValues)
				for (int[] tuple : tuples)
					sups0[tuple[0]][tuple[1] / Long.SIZE] &= Bit.ONE_LONG_BIT_TO_0[tuple[1] % Long.SIZE];
			else
				for (int[] tuple : tuples) {
					int val0 = dom0.toIdx(tuple[0]), val1 = dom1.toIdx(tuple[1]);
					sups0[val0][val1 / Long.SIZE] &= Bit.ONE_LONG_BIT_TO_0[val1 % Long.SIZE];
				}
		}
		// Now, we fill up bitSups1
		for (int i = 0; i < sups0.length; i++) {
			int iByte = i / Long.SIZE, iPos = i % Long.SIZE;
			for (int j = 0; j < sups0[i].length; j++) {
				long support = sups0[i][j];
				for (int k = 0; k < Math.min(Long.SIZE, sups1.length - j * Long.SIZE); k++)
					if ((support & Bit.ONE_LONG_BIT_TO_1[k]) != 0)
						sups1[j * Long.SIZE + k][iByte] |= Bit.ONE_LONG_BIT_TO_1[iPos];
			}
		}
		this.sharing = saveSpace(c.problem, sups0, sups1);
		buildFilters();
	}

	@Override
	public int[] computeVariableSymmetryMatching(ConstraintExtension c) {
		if (!Variable.haveSameDomainType(c.scp))
			return new int[] { 1, 2 };
		for (int i = 0; i < sups0.length; i++)
			for (int j = i + 1; j < sups0.length; j++) {
				boolean b1 = (sups0[i][j / Long.SIZE] & Bit.ONE_LONG_BIT_TO_1[j % Long.SIZE]) != 0;
				boolean b2 = (sups0[j][i / Long.SIZE] & Bit.ONE_LONG_BIT_TO_1[i % Long.SIZE]) != 0;
				if (b1 != b2)
					return new int[] { 1, 2 };
			}
		return new int[] { 1, 1 };
	}

	public int[][] computeValueSymmetryMatching() {
		int[][] m = Variable.litterals(firstRegisteredCtr().scp).intArray();
		int color = 1;
		for (int i = 0; i < m.length; i++)
			for (int j = 0; j < m[i].length; j++)
				if (m[i][j] == 0) {
					long[] s1 = i == 0 ? sups0[j] : sups1[j];
					for (int k = i; k < m.length; k++)
						for (int l = k == i ? j + 1 : 0; l < m[k].length; l++)
							if (m[k][l] == 0 && (s1 == (k == 0 ? sups0[l] : sups1[l])))
								m[k][l] = color;
					m[i][j] = color++;
				}
		return m;
	}

	@Override
	public boolean removeTuple(int[] tuple) {
		assert registeredCtrs().size() == 1 && !sharing;
		if ((sups0[tuple[0]][tuple[1] / Long.SIZE] & Bit.ONE_LONG_BIT_TO_1[tuple[1] % Long.SIZE]) == 0)
			return false;
		assert sups1 == null || (sups1[tuple[1]][tuple[0] / Long.SIZE] & Bit.ONE_LONG_BIT_TO_1[tuple[0] % Long.SIZE]) != 0;
		sups0[tuple[0]][tuple[1] / Long.SIZE] &= Bit.ONE_LONG_BIT_TO_0[tuple[1] % Long.SIZE];
		if (sups1 != null)
			sups1[tuple[1]][tuple[0] / Long.SIZE] &= Bit.ONE_LONG_BIT_TO_0[tuple[0] % Long.SIZE];
		incrementNbTuplesRemoved();
		return true;
	}

	@Override
	public String toString() {
		int size0 = firstRegisteredCtr().scp[0].dom.initSize(), size1 = firstRegisteredCtr().scp[1].dom.initSize();
		String s0 = "Bits of " + firstRegisteredCtr() + "\n"
				+ IntStream.range(0, sups0.length).mapToObj(i -> "\t" + i + " : " + Bit.decrypt(sups0[i], size1) + "\n").collect(Collectors.joining());
		String sd0 = "Dense Bits of " + firstRegisteredCtr() + "\n"
				+ IntStream.range(0, sups0Filtered.length).mapToObj(i -> "\t" + i + " : " + Kit.join(sups0Filtered[i]) + "\n").collect(Collectors.joining());
		String s1 = "Bits of " + firstRegisteredCtr() + "\n"
				+ IntStream.range(0, sups1.length).mapToObj(i -> "\t" + i + " : " + Bit.decrypt(sups1[i], size0) + "\n").collect(Collectors.joining());
		String sd1 = "Dense Bits of " + firstRegisteredCtr() + "\n"
				+ IntStream.range(0, sups1Filtered.length).mapToObj(i -> "\t" + i + " : " + Kit.join(sups1Filtered[i]) + "\n").collect(Collectors.joining());
		return s0 + sd0 + s1 + sd1;
	}
}

// public void storeTuplesAndUpdateConflictsStructure(String[] canonicalPredicate) {
// assert getNbDependentCtrs() == 1;
// buildArrays();
// Constraint ctr = getFirstDependentCtr();
// Domain domain0 = ctr.scp[0].dom, domain1 = ctr.scp[1].dom;
// int[][] nbConflicts = ctr.getConflictsStructure().getNbConflicts();
// EvaluationManager evaluationManager = new EvaluationManager(Symbolic.replaceSymbols(ctr.pb.symbolic,
// canonicalPredicate));
// int cnt = 0;
// int[] tmp = ctr.tupleManager.localTuple;
// for (int i = 0; i < domain0.initSize(); i++) {
// tmp[0] = domain0.toVal(i);
// for (int j = 0; j < domain1.initSize(); j++) {
// tmp[1] = domain1.toVal(j);
// cnt++;
// if (evaluationManager.evaluate(tmp) == 1) {
// supports0[i][j / Long.SIZE] |= Bit.ONE_LONG_BIT_TO_1[j % Long.SIZE];
// supports1[j][i / Long.SIZE] |= Bit.ONE_LONG_BIT_TO_1[i % Long.SIZE];
// } else {
// nbConflicts[0][i]++;
// nbConflicts[1][j]++;
// }
// }
// }
// ctr.pb.stuff.nConvertionCcks += cnt;
// saveSpace();
// ctr.getConflictsStructure().computeNbMaxConflicts();
// assert ctr.getConflictsStructure().controlStructures();
// }
