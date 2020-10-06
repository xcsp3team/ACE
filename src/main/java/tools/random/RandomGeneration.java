/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package tools.random;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.Random;
import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import utility.Kit;
import utility.operations.Base;
import utility.sets.SetSparse;

/**
 * This class allows generating integer random lists. A random list is formed of fixed-size tuples, the values of which range from 0 to a limit given
 * by the user. When generating random lists, it is possible to indicate:
 * <ul>
 * <li>if the same tuple can occur several times,
 * <li>if the same value can occur several times in a generated tuple,
 * <li>if the lists must or must not contain a particular tuple.
 * </ul>
 */
public abstract class RandomGeneration {

	/**
	 * The number of possible values for each element of the tuples of the generated lists. The array index corresponds to the order of the elements
	 * of the tuples. The array value gives the number of values for the corresponding element. For instance, if nbValues[i] = n then it means that
	 * the ith element of each tuple can belong to the set <code> {0,1,...,n-1} </code>.
	 */
	protected final int[] nValues;

	/**
	 * The seed used to generate random numbers.
	 */
	protected final long seed;

	/**
	 * The <code> Random </code> object used to generate lists.
	 */
	protected final Random random;

	/**
	 * A particular tuple, which if not <code> null </code>, must or must not belong to the generated lists.
	 */
	protected int[] fixedTuple;

	/**
	 * Indicates if the fixed tuple, if not <code> null </code>, must or must not belong to the generated lists.
	 */
	protected boolean fixedTupleIsSupport;

	/**
	 * Builds a random list generator.
	 * 
	 * @param nValues
	 *            the number of values for each element of the tuples
	 * @param seed
	 *            the seed used to generate random numbers
	 */
	public RandomGeneration(int[] nValues, long seed) {
		this.nValues = nValues;
		this.seed = seed;
		this.random = new Random(seed);

	}

	/**
	 * Builds a random list generator.
	 * 
	 * @param nValues
	 *            the uniform number of values used to build tuples
	 * @param arity
	 *            the length of each tuple
	 * @param seed
	 *            the seed used to generate random numbers
	 */
	public RandomGeneration(int nValues, int arity, long seed) {
		this(Kit.repeat(nValues, arity), seed);
	}

	public int arity() {
		return nValues.length;
	}

	private static BigInteger nPermutableCombinations(SetSparse takenValues, int[] nValues, int j) {
		// TODO needs a cache for becoming efficient
		int[] freeValues = IntStream.range(0, nValues[j]).filter(v -> !takenValues.isPresent(v)).toArray();
		if (j == nValues.length - 1)
			return BigInteger.valueOf(freeValues.length);
		BigInteger sum = BigInteger.ZERO;
		for (int v : freeValues) {
			takenValues.add(v);
			sum = sum.add(nPermutableCombinations(takenValues, nValues, j + 1));
			takenValues.remove(v);
		}
		return sum;
	}

	private static BigInteger nPermutableCombinationsFor(int[] nValues) {
		if (IntStream.range(1, nValues.length).allMatch(i -> nValues[i] == nValues[0])) {
			BigInteger k = Utilities.binomialBig(nValues[0], nValues.length);
			return k.multiply(Utilities.factorialBig(nValues.length));
		}
		return nPermutableCombinations(new SetSparse(IntStream.of(nValues).max().getAsInt()), nValues, 0);
	}

	protected BigInteger nDistinctTuples(boolean valueRepetition) {
		return valueRepetition ? Utilities.nArrangementsFor(nValues) : nPermutableCombinationsFor(nValues);
	}

	public static void main(String[] args) {
		// int[] t = IntStream.of(4, 4, 4, 4, 4).toArray();
		// int[] t = IntStream.of(4, 4, 4, 20, 20, 20, 20, 10, 10, 10, 10, 10, 10, 10).toArray();
		int[] t = IntStream.of(2, 2, 6, 10, 23).toArray();
		System.out.println("Combinations = " + nPermutableCombinationsFor(t) + "\nArrangements = " + Utilities.nArrangementsFor(t));
		// System.out.println("f=" + f(t));
	}

	// ************************************************************************
	// ***** RandomGenerationProb
	// ************************************************************************

	/**
	 * This class allows generating integer random lists using a probability model. All potential tuples are selected according a probability given by
	 * the user. With this model, generated lists are unstructured and tuples can not occur several times.
	 */
	public static final class RandomGenerationProb extends RandomGeneration {

		private static BigInteger N_TUPLES_LIMIT = BigInteger.valueOf(1000000000);

		/**
		 * Builds a probability random list generator.
		 * 
		 * @param nValues
		 *            the number of values for each element of the tuples
		 * @param seed
		 *            the seed used to generate random numbers
		 */
		public RandomGenerationProb(int[] nValues, long seed) {
			super(nValues, seed);
			BigInteger nDistinctTuples = Utilities.nArrangementsFor(nValues);
			Kit.control(nDistinctTuples.compareTo(BigInteger.ZERO) > 0 && nDistinctTuples.compareTo(N_TUPLES_LIMIT) < 0,
					() -> "The number of distinct tuples is not valid ");
		}

		/**
		 * Generates and returns a random list of integer tuples.
		 * 
		 * @param selectionLimit
		 *            the limit (a real value ranging from 0 to 1) used for selection
		 * @param valueRepetition
		 *            indicates if the same value can occur several times in a tuple
		 * @param fixedTuple
		 *            a particular tuple, which if not <code> null </code>, must or must not belong to the generated lists
		 * @param fixedTupleIsSupport
		 *            indicates if the fixed tuple, if not <code> null </code>, must or must not belong to the generated lists
		 * @return an random generated list of integer tuples
		 */
		public int[][] selectTuples(double selectionLimit, int[] fixedTuple, boolean fixedTupleIsSupport) {
			int nDistinctTuples = Utilities.nArrangementsFor(nValues).intValueExact();
			LinkedList<int[]> list = new LinkedList<>();
			long fixedIndex = fixedTuple == null ? -1 : Base.decimalValueFor(fixedTuple, nValues);
			int[] tuple = new int[arity()];
			for (int i = 0; i < nDistinctTuples; i++) {
				Base.valueFor(i, tuple, nValues);
				if ((Base.decimalValueFor(tuple, nValues) == fixedIndex && fixedTupleIsSupport)
						|| (Base.decimalValueFor(tuple, nValues) != fixedIndex && random.nextDouble() <= selectionLimit))
					list.add(tuple.clone());
			}
			return Kit.sort(list.toArray(new int[0][]), Utilities.lexComparatorInt);
		}
	}

	// ************************************************************************
	// ***** RandomGenerationProp
	// ************************************************************************

	/**
	 * This class allows generating integer random lists using a proportion model. A given fixed number of tuples is randomly generated.
	 */
	public static final class RandomGenerationProp extends RandomGeneration {
		private static final int OCCURENCES_LIMIT = 100;
		private static final int RANDOMS_LIMIT = 4;
		private static final int OVERFLOWS_LIMIT = 35;

		public enum TypeList {
			UNSTRUCTURED, // Constant for denoting that generated lists have no structure, i.e., are purely random.
			CONNECTED, // Constant for denoting that each value must occur at least in one tuple of the generated lists.
			BALANCED; // Constant for denoting that generated lists must be balanced, i.e., all values have the same number of occurrences in the
						// different tuples of the generated lists.
			public static TypeList get(int i) {
				return i == 0 ? UNSTRUCTURED : i == 1 ? CONNECTED : BALANCED;
			}
		};

		/**
		 * Indicates if the same value can occur several times in a generated tuple.
		 */
		protected boolean valueRepetition;

		/**
		 * Indicates if the same tuple can occur several times in the generated lists.
		 */
		protected boolean tupleRepetition;

		/**
		 * The wished number of occurrences of each value.
		 */
		protected int lowerbound;

		/**
		 * The maximum number of occurrences of each value.
		 */
		protected int upperbound;

		/**
		 * The number of allowed overflows wrt the maximum number of occurrences of each value.
		 */
		protected int nAllowedOverflows;

		/**
		 * The current number of overflows wrt the maximum number of occurrences of each value.
		 */
		private int nOverflows, nOverflowsBis;

		/**
		 * The number of occurrences of each value in the generated lists.
		 */
		private final int[] nOccurences, nOccurencesBis;

		/**
		 * Builds a proportion random list generator.
		 * 
		 * @param nValues
		 *            the number of values for each element of the tuples
		 * @param seed
		 *            the seed used to generate random numbers
		 */
		public RandomGenerationProp(int[] nValues, long seed) {
			super(nValues, seed);
			this.nOccurences = new int[IntStream.of(nValues).max().orElse(-1)];
			this.nOccurencesBis = new int[nOccurences.length];
		}

		/**
		 * Builds a proportion random list generator.
		 * 
		 * @param nValues
		 *            the uniform number of values used to build tuples
		 * @param arity
		 *            the length of each tuple
		 * @param seed
		 *            the seed used to generate random numbers
		 */
		public RandomGenerationProp(int nValues, int arity, long seed) {
			this(Kit.repeat(nValues, arity), seed);
		}

		/**
		 * Saves the current number of occurences of each value and the current number of overflows.
		 */
		protected void storeNbOccurrences() {
			System.arraycopy(nOccurences, 0, nOccurencesBis, 0, nOccurences.length);
			nOverflowsBis = nOverflows;
		}

		/**
		 * Restores the current number of occurences of each value and the current number of overflows.
		 */
		protected void restoreNbOccurrences() {
			System.arraycopy(nOccurencesBis, 0, nOccurences, 0, nOccurences.length);
			nOverflows = nOverflowsBis;
		}

		/**
		 * Fixes some limits, according to the given type, about the generation of tuples.
		 * 
		 * @param type
		 *            the type of the generated lists which can be UNSTRUCTURED, CONNECTED or BALANCED
		 */
		protected final void setLimits(int nTuples, TypeList type) {
			int size = arity() * nTuples;
			if (type == TypeList.UNSTRUCTURED) {
				lowerbound = Integer.MAX_VALUE; // this way, no restriction is imposed
				upperbound = Integer.MAX_VALUE;
				nAllowedOverflows = 0;
			}
			if (type == TypeList.CONNECTED) {
				lowerbound = 1;
				upperbound = Integer.MAX_VALUE;
				nAllowedOverflows = size - (lowerbound * nOccurences.length);
			}
			if (type == TypeList.BALANCED) {
				lowerbound = size / nOccurences.length;
				upperbound = lowerbound + 1;
				nAllowedOverflows = size % nOccurences.length;
				Kit.control(lowerbound > 0);
			}
		}

		private boolean isValidValue(int[] tuple, int position) {
			int value = tuple[position];
			if (!valueRepetition)
				for (int i = 0; i < position; i++)
					if (tuple[i] == value)
						return false;
			if (nOccurences[value] + 1 > upperbound || (nOccurences[value] + 1 > lowerbound && nOverflows + 1 > nAllowedOverflows)) {
				assert nOccurences[value] <= upperbound && nOverflows <= nAllowedOverflows;
				return false;
			}
			nOccurences[value]++;
			if (nOccurences[value] > lowerbound)
				nOverflows++;
			return true;
		}

		private boolean canBeInserted(int[][] tuples, int i) {
			if (fixedTuple != null && !fixedTupleIsSupport && Arrays.equals(tuples[i], fixedTuple))
				return false;
			if (i > 0) {
				int position = Arrays.binarySearch(tuples, 0, i, tuples[i], Utilities.lexComparatorInt);
				if (position >= 0 && !tupleRepetition)
					return false; // because already present
				// we insert the tuple at the right place
				position = position >= 0 ? position : (-position - 1);
				int[] tmp = tuples[i];
				for (int j = i - 1; j >= position; j--)
					tuples[j + 1] = tuples[j];
				tuples[position] = tmp;
			}
			return true;
		}

		private void doPotentialRelaxation(int nTrials) {
			if (nTrials % OCCURENCES_LIMIT == 0)
				upperbound++;
			else if (nTrials % OVERFLOWS_LIMIT == 0)
				nAllowedOverflows++;
		}

		/**
		 * Makes the selection of the given number of tuples.
		 */
		protected int[][] makeSelection(int nTuples, TypeList type) {
			setLimits(nTuples, type);
			int[][] tuples = new int[nTuples][arity()];
			if (fixedTuple != null && fixedTupleIsSupport) {
				// Keep this next instruction to have counters related to occurrences updated.
				Kit.control(IntStream.range(0, fixedTuple.length).allMatch(i -> isValidValue(fixedTuple, i)),
						() -> " keep absolutely in order to update counters");
				System.arraycopy(fixedTuple, 0, tuples[0], 0, fixedTuple.length);
			}
			for (int i = fixedTuple != null && fixedTupleIsSupport ? 1 : 0; i < tuples.length; i++) {
				storeNbOccurrences();
				int nTrials = 0;
				do {
					boolean valid = false;
					while (!valid) {
						restoreNbOccurrences();
						valid = true;
						for (int j = 0; valid && j < tuples[i].length; j++) {
							int nRandomAttempts = 0;
							do {
								tuples[i][j] = random.nextInt(nValues[j]);
							} while (!isValidValue(tuples[i], j) && nRandomAttempts++ < (RANDOMS_LIMIT * nValues[j]));
							if (nRandomAttempts >= RANDOMS_LIMIT * nValues[j])
								valid = false;
						}
						if (!valid)
							doPotentialRelaxation(++nTrials);
						else if (!valueRepetition)
							Arrays.sort(tuples[i]);
					}
				} while (!canBeInserted(tuples, i));
			}
			return tuples;
		}

		/**
		 * Generates and returns a random list.
		 * 
		 * @param nTuples
		 *            the number of tuples to be selected
		 * @param type
		 *            the type of the generated lists which can be UNSTRUCTURED, CONNECTED or BALANCED
		 * @param tupleRepetition
		 *            indicates if the same tuple can occur several times in the generated lists
		 * @param valueRepetition
		 *            indicates if the same value can occur several times in a generated tuple
		 * @param fixedTuple
		 *            a particular tuple, which if not <code> null </code>, must or must not belong to the generated lists
		 * @param fixedTupleIsSupport
		 *            indicates if the fixed tuple, if not <code> null </code>, must or must not belong to the generated lists
		 * @return a random generated list
		 */
		public int[][] selectTuples(int nTuples, TypeList type, boolean tupleRepetition, boolean valueRepetition, int[] fixedTuple,
				boolean fixedTupleIsSupport) {
			// System.out.println("selectTuples1 " + nTuples + " " + type + " " + tupleRepetition + " " + valueRepetition);
			this.tupleRepetition = tupleRepetition;
			this.valueRepetition = valueRepetition;
			this.fixedTuple = fixedTuple;
			this.fixedTupleIsSupport = fixedTupleIsSupport;

			BigInteger nDistinctTuples = Utilities.nArrangementsFor(nValues);
			Kit.control(nDistinctTuples.compareTo(BigInteger.ZERO) > 0, () -> "The number of distinct tuples is equal to 0 " + valueRepetition);
			Kit.control(tupleRepetition || BigInteger.valueOf(nTuples).compareTo(nDistinctTuples) <= 0,
					() -> "The number of tuples " + nTuples + " is greater than the maximum possible number ");
			Kit.control(fixedTuple == null || valueRepetition || IntStream.range(0, fixedTuple.length - 1).allMatch(i -> fixedTuple[i] < fixedTuple[i + 1]),
					() -> "The fixed tuple must be ordered");

			int[][] tuples = makeSelection(nTuples, type);
			return Kit.sort(tuples, Utilities.lexComparatorInt);
		}

		/**
		 * Generates and returns a random list.
		 * 
		 * @param nTuples
		 *            the number of tuples to be selected
		 * @param type
		 *            the type of the generated lists which can be UNSTRUCTURED, CONNECTED or BALANCED
		 * @param tupleRepetition
		 *            indicates if the same tuple can occur several times in the generated lists
		 * @param valueRepetition
		 *            indicates if the same value can occur several times in a generated tuple
		 * @return a random generated list
		 */
		public final int[][] selectTuples(int nTuples, TypeList type, boolean tupleRepetition, boolean valueRepetition) {
			return selectTuples(nTuples, type, tupleRepetition, valueRepetition, null, false);
		}

		public final int[][] selectSets(int nSets, TypeList type, boolean repetition) {
			return selectTuples(nSets, type, repetition, false);
		}

	}
}
