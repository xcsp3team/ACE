/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension.structures;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import main.Head;
import problem.Problem;
import utility.Bit;
import utility.Kit;
import utility.Kit.LongArrayHashKey;
import variables.Domain;
import variables.Variable;

public final class Bits extends ExtensionStructure {

	// used to share arrays so as to save space TODO tune the constant
	public static final Map<LongArrayHashKey, long[]> globalMap = Collections.synchronizedMap(new HashMap<LongArrayHashKey, long[]>(2000));

	// long integers are used to store the indication that there is a support (bit set to 1) or not (bit set to 0)
	private long[][] bitSups0, bitSups1;

	private int[][] bitSups0Dense, bitSups1Dense;

	private boolean sharedArrays;

	private LongArrayHashKey hashKey;

	public long[][] bitSupsFor(int vap) {
		return vap == 0 ? bitSups0 : bitSups1;
	}

	public int[][] bitSupsDenseFor(int vap) {
		return vap == 0 ? bitSups0Dense : bitSups1Dense;
	}

	private void buildArrays() {
		Domain dom0 = firstRegisteredCtr().scp[0].dom, dom1 = firstRegisteredCtr().scp[1].dom;
		bitSups0 = new long[dom0.initSize()][dom1.initSize() / Long.SIZE + (dom1.initSize() % Long.SIZE != 0 ? 1 : 0)];
		bitSups1 = new long[dom1.initSize()][dom0.initSize() / Long.SIZE + (dom0.initSize() % Long.SIZE != 0 ? 1 : 0)];
	}

	private void fillSupports0(int[][] tuples, boolean positive) {
		Constraint ctr = firstRegisteredCtr();
		Domain dom0 = ctr.scp[0].dom, dom1 = ctr.scp[1].dom;
		if (positive) {
			if (ctr.indexesMatchValues)
				for (int[] tuple : tuples)
					bitSups0[tuple[0]][tuple[1] / Long.SIZE] |= Bit.ONE_LONG_BIT_TO_1[tuple[1] % Long.SIZE];
			else
				for (int[] tuple : tuples) {
					int val0 = dom0.toIdx(tuple[0]), val1 = dom1.toIdx(tuple[1]);
					bitSups0[val0][val1 / Long.SIZE] |= Bit.ONE_LONG_BIT_TO_1[val1 % Long.SIZE];
				}
		} else {
			for (long[] t : bitSups0) {
				Arrays.fill(t, Bit.ALL_LONG_BITS_TO_1);
				int remainder = dom1.initSize() % Long.SIZE;
				if (remainder != 0)
					t[t.length - 1] = Bit.bitsA1To(remainder);
			}
			if (ctr.indexesMatchValues)
				for (int[] tuple : tuples)
					bitSups0[tuple[0]][tuple[1] / Long.SIZE] &= Bit.ONE_LONG_BIT_TO_0[tuple[1] % Long.SIZE];
			else
				for (int[] tuple : tuples) {
					int val0 = dom0.toIdx(tuple[0]), val1 = dom1.toIdx(tuple[1]);
					bitSups0[val0][val1 / Long.SIZE] &= Bit.ONE_LONG_BIT_TO_0[val1 % Long.SIZE];
				}
		}
	}

	private void fillSupports1() {
		for (int i = 0; i < bitSups0.length; i++) {
			int iByte = i / Long.SIZE, iPos = i % Long.SIZE;
			for (int j = 0; j < bitSups0[i].length; j++) {
				long support = bitSups0[i][j];
				for (int k = 0; k < Math.min(Long.SIZE, bitSups1.length - j * Long.SIZE); k++)
					if ((support & Bit.ONE_LONG_BIT_TO_1[k]) != 0)
						bitSups1[j * Long.SIZE + k][iByte] |= Bit.ONE_LONG_BIT_TO_1[iPos];
			}
		}
	}

	private void saveSpace(long[][] supports, int id) {
		Problem problem = firstRegisteredCtr().pb;
		for (int i = 0; i < supports.length; i++) {
			if (hashKey == null)
				hashKey = new LongArrayHashKey();
			hashKey.t = supports[i];
			long[] tt = null;
			synchronized (globalMap) {
				tt = globalMap.get(hashKey);
			}
			if (tt == null) {
				synchronized (globalMap) {
					globalMap.put(hashKey, supports[i]);
				}
				hashKey = null;
			} else {
				supports[i] = tt;
				problem.stuff.nSharedBinaryRepresentations++;
			}
		}
	}

	private void saveSpace() {
		Head resolution = firstRegisteredCtr().pb.head;
		if (resolution.control.settingProblem.shareBitVectors) {
			int nSharedRepresentationsBefore = firstRegisteredCtr().pb.stuff.nSharedBinaryRepresentations;
			saveSpace(bitSups0, 1);
			saveSpace(bitSups1, 0);
			sharedArrays = (firstRegisteredCtr().pb.stuff.nSharedBinaryRepresentations - nSharedRepresentationsBefore) > 0;
		}
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		buildArrays();
		fillSupports0(tuples, positive);
		fillSupports1();
		saveSpace();
		bitSups0Dense = Stream.of(bitSups0).map(t -> IntStream.range(0, t.length).filter(i -> t[i] != 0L).toArray()).toArray(int[][]::new);
		bitSups1Dense = Stream.of(bitSups1).map(t -> IntStream.range(0, t.length).filter(i -> t[i] != 0L).toArray()).toArray(int[][]::new);
	}

	// public void storeTuplesAndUpdateConflictsStructure(String[] canonicalPredicate) {
	// assert getNbDependentCtrs() == 1;
	// buildArrays();
	// Constraint ctr = getFirstDependentCtr();
	// Domain domain0 = ctr.scp[0].dom, domain1 = ctr.scp[1].dom;
	// int[][] nbConflicts = ctr.getConflictsStructure().getNbConflicts();
	// EvaluationManager evaluationManager = new EvaluationManager(Symbolic.replaceSymbols(ctr.pb.symbolic, canonicalPredicate));
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

	@Override
	public int[] computeVariableSymmetryMatching() {
		if (!Variable.haveSameDomainType(firstRegisteredCtr().scp))
			return new int[] { 1, 2 };
		for (int i = 0; i < bitSups0.length; i++)
			for (int j = i + 1; j < bitSups0.length; j++) {
				boolean b = (bitSups0[i][j / Long.SIZE] & Bit.ONE_LONG_BIT_TO_1[j % Long.SIZE]) != 0;
				boolean c = (bitSups0[j][i / Long.SIZE] & Bit.ONE_LONG_BIT_TO_1[i % Long.SIZE]) != 0;
				if (b != c)
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
					long[] s1 = i == 0 ? bitSups0[j] : bitSups1[j];
					for (int k = i; k < m.length; k++)
						for (int l = k == i ? j + 1 : 0; l < m[k].length; l++)
							if (m[k][l] == 0 && (s1 == (k == 0 ? bitSups0[l] : bitSups1[l])))
								m[k][l] = color;
					m[i][j] = color++;
				}
		return m;
	}

	public Bits(Constraint ctr) {
		super(ctr);
		Kit.control(ctr.scp.length == 2);
	}

	public Bits(Constraint ctr, Bits bits) {
		this(ctr);
		bitSups0 = Kit.cloneDeeply(bits.bitSups0);
		bitSups1 = Kit.cloneDeeply(bits.bitSups1);
		sharedArrays = bits.sharedArrays;
	}

	public boolean hasSameSupportsThan(Bits bits) {
		if (bitSups0.length != bits.bitSups0.length || bitSups1.length != bits.bitSups1.length)
			return false;
		for (int i = 0; i < bitSups0.length; i++)
			for (int j = 0; j < bitSups0[i].length; j++)
				if (bitSups0[i][j] != bits.bitSups0[i][j])
					return false;
		return true;
	}

	/**
	 * This method returns true iff all pairs of variable assignments corresponding to the tuple are compatible.
	 */
	@Override
	public final boolean checkIdxs(int[] idxs) {
		return (bitSups0[idxs[0]][idxs[1] / Long.SIZE] & Bit.ONE_LONG_BIT_TO_1[idxs[1] % Long.SIZE]) != 0; // Bit.ALL_LONG_BITS_TO_0;
		// return (supports1[tuple[1]][tuple[0] / Long.SIZE] & Bit.ONE_LONG_BIT_TO_1[tuple[0] % Long.SIZE]) != 0;
	}

	@Override
	public boolean removeTuple(int[] tuple) {
		assert registeredCtrs().size() == 1 && !sharedArrays;
		if ((bitSups0[tuple[0]][tuple[1] / Long.SIZE] & Bit.ONE_LONG_BIT_TO_1[tuple[1] % Long.SIZE]) == 0) // BitManager.ALL_LONG_BITS_TO_0)
			return false;
		assert bitSups1 == null || (bitSups1[tuple[1]][tuple[0] / Long.SIZE] & Bit.ONE_LONG_BIT_TO_1[tuple[0] % Long.SIZE]) != 0; // BitManager.ALL_LONG_BITS_TO_0;
		bitSups0[tuple[0]][tuple[1] / Long.SIZE] &= Bit.ONE_LONG_BIT_TO_0[tuple[1] % Long.SIZE];
		if (bitSups1 != null)
			bitSups1[tuple[1]][tuple[0] / Long.SIZE] &= Bit.ONE_LONG_BIT_TO_0[tuple[0] % Long.SIZE];
		incrementNbTuplesRemoved();
		return true;
	}

	@Override
	public String toString() {
		int size0 = firstRegisteredCtr().scp[0].dom.initSize(), size1 = firstRegisteredCtr().scp[1].dom.initSize();

		String s0 = "Bits of " + firstRegisteredCtr() + "\n"
				+ IntStream.range(0, bitSups0.length).mapToObj(i -> "\t" + i + " : " + Bit.decrypt(bitSups0[i], size1) + "\n").collect(Collectors.joining());
		String sd0 = "Dense Bits of " + firstRegisteredCtr() + "\n"
				+ IntStream.range(0, bitSups0Dense.length).mapToObj(i -> "\t" + i + " : " + Kit.join(bitSups0Dense[i]) + "\n").collect(Collectors.joining());
		String s1 = "Bits of " + firstRegisteredCtr() + "\n"
				+ IntStream.range(0, bitSups1.length).mapToObj(i -> "\t" + i + " : " + Bit.decrypt(bitSups1[i], size0) + "\n").collect(Collectors.joining());
		String sd1 = "Dense Bits of " + firstRegisteredCtr() + "\n"
				+ IntStream.range(0, bitSups1Dense.length).mapToObj(i -> "\t" + i + " : " + Kit.join(bitSups1Dense[i]) + "\n").collect(Collectors.joining());

		// StringBuilder sb = new StringBuilder("Bits of " + firstRegisteredCtr() + "\n");
		// sb.append(" support0\n");
		// for (int i = 0; i < supports0.length; i++)
		// sb.append(" " + i + " : " + Bit.decrypt(supports0[i], size1) + "\n");
		// if (supports1 != null) {
		// sb.append(" support1\n");
		// for (int i = 0; i < supports1.length; i++)
		// sb.append(" " + i + " : " + Bit.decrypt(supports1[i], size0) + "\n");
		// }

		return s0 + sd0 + s1 + sd1; // sb.toString();
	}
}
