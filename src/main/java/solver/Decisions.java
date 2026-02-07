/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package solver;

import static utility.Kit.control;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

import interfaces.Observers.ObserverOnAssignments;
import interfaces.Observers.ObserverOnRuns;
import sets.SetDense;
import solver.Decisions.Decoder.Decoder1;
import solver.Decisions.Decoder.Decoder2;
import utility.Bit;
import utility.Kit;
import variables.Domain;
import variables.Variable;

import static java.lang.Math.log;
import static java.lang.Math.ceil;

/**
 * This object allows us to store the set of decisions taken by the solver during search. <br />
 * Each decision is currently encoded under the form of an int. <br/>
 * IMPORTANT: it is planned in the future to represent each decision with a long instead of an int.
 * 
 * @author Christophe Lecoutre
 */
public final class Decisions implements ObserverOnRuns, ObserverOnAssignments {

	/**********************************************************************************************
	 * Implementing interface
	 *********************************************************************************************/

	@Override
	public void afterRun() {
		set.clear();
	}

	@Override
	public void afterAssignment(Variable x, int a) {
		// Adds a positive decision x=a to the current store
		set.add(decoder.positiveDecisionFor(x.num, a));
		Bit.setTo0(failedAssignments, set.limit);
		assert controlDecisions();

	}

	@Override
	public void afterFailedAssignment(Variable x, int a) {
	}

	@Override
	public void afterUnassignment(Variable x) {
		// deletes the last positive decision from the store as well as any potential negative decisions following it
		int[] dense = set.dense;
		int limit = set.limit;
		if (dense[limit] > 0)
			Bit.setTo1(failedAssignments, limit);
		else
			while (dense[limit] < 0)
				limit--; // for discarding the negative decisions that follow the positive decision
		assert dense[limit] > 0 && decoder.varIn(dense[limit]) == x : toString();
		set.limit = limit - 1; // -1 for discarding the positive decision
	}

	/**********************************************************************************************
	 * Coding/decoding decisions
	 *********************************************************************************************/

	public static abstract class Decoder {

		protected final Solver solver;

		/**
		 * The variables of the problem (redundant field)
		 */
		protected final Variable[] variables;

		public int x;

		public int a;

		protected Decoder(Solver solver) {
			this.solver = solver;
			this.variables = solver.problem.variables;
		}

		/**
		 * Returns the code for the specified positive decision
		 * 
		 * @param x
		 *            the (number of the) variable involved in the positive decision
		 * @param a
		 *            the index (of value) involved in the positive decision
		 * @return the code for the specified positive decision
		 */
		public abstract int positiveDecisionFor(int x, int a);

		/**
		 * Returns the code for the specified negative decision
		 * 
		 * @param x
		 *            the (number of the) variable involved in the negative decision
		 * @param a
		 *            the index (of value) involved in the negative decision
		 * @return the code for the specified negative decision
		 */
		public abstract int negativeDecisionFor(int x, int a);

		public abstract Decoder set(int decision);

		public final boolean apply(int decision) {
			set(decision);
			Domain dom = variables[x].dom;
			return decision > 0 ? dom.reduceTo(a) : dom.removeIfPresent(a);
		}

		public final boolean canBeValid(int decision) {
			assert decision != 0;
			set(decision);
			Domain dom = variables[x].dom;
			return decision > 0 ? dom.contains(a) : dom.size() > 1 || !dom.contains(a);
		}

		public final boolean containsIdx(int decision) {
			set(decision);
			return variables[x].dom.contains(a);
		}

		protected Variable varIn(int decision) {
			set(decision);
			return variables[x];
		}

		/**
		 * Returns the string representation of the decision whose code is specified
		 * 
		 * @param decision
		 *            the code of a decision
		 * @return the string representation of the decision whose code is specified
		 */
		public final String stringOf(int decision) {
			assert decision != 0;
			Variable x = varIn(decision);
			return x + (decision > 0 ? "=" : "!=") + x.dom.toVal(a);// + (valIn(dec) != idxIn(dec) ? "(" + idxIn(dec) + ")" : "");
		}

		public static final class Decoder1 extends Decoder {

			private final int OFFSET;

			protected Decoder1(Solver solver) {
				super(solver);
				int n1 = (int) ceil(log(variables.length) / log(2));
				int n2 = (int) ceil(log(solver.problem.features.maxDomSize()) / log(2));
				control(n1 + n2 < 31, () -> "Cannot represent decisions " + n1 + " " + n2);
				this.OFFSET = (int) Math.pow(2, n2 + 1); // +1 because 0 excluded ???
			}

			@Override
			public final int positiveDecisionFor(int x, int a) {
				return 1 + a + OFFSET * x;
			}

			@Override
			public final int negativeDecisionFor(int x, int a) {
				return -(1 + a + OFFSET * x);
			}

			public Decoder set(int decision) {
				this.x = Math.abs(decision) / OFFSET;
				this.a = Math.abs(decision) % OFFSET - 1;
				return this;
			}
		}

		public static final class Decoder2 extends Decoder {

			private final int[] offsets;

			private final int[][] slices;

			private final int[] starts;

			protected Decoder2(Solver solver) {
				super(solver);
				List<int[]> list = new ArrayList<>();
				this.offsets = new int[variables.length];
				int sum = 0, start = 0, length = -1, nb = 0, pos = 0;
				for (int i = 0; i < variables.length; i++) {
					int size = variables[i].dom.initSize();
					if (sum == 0) {
						start = sum;
						length = size;
						nb = 1;
						pos = i;
					} else if (size == length)
						nb++;
					else {
						list.add(new int[] { start, length, nb, pos });
						start = sum;
						length = size;
						nb = 1;
						pos = i;
					}
					offsets[i] = sum;
					sum += size;
				}
				list.add(new int[] { start, length, nb, pos });
				slices = list.stream().toArray(int[][]::new);
				starts = list.stream().mapToInt(sl -> sl[0]).toArray();
				// System.out.println("slices " + Kit.join(slices));
				// System.out.println("starts " + Kit.join(starts));
			}

			@Override
			public final int positiveDecisionFor(int x, int a) {
				return 1 + offsets[x] + a;
			}

			@Override
			public final int negativeDecisionFor(int x, int a) {
				return -(1 + offsets[x] + a);
			}

			public Decoder set(int decision) {
				int absdec = Math.abs(decision) - 1;
				int left = 0, right = starts.length - 1;
				while (left + 1 < right) {
					int mid = (left + right) / 2;
					if (starts[mid] <= absdec)
						left = mid;
					else
						right = mid;
				}
				if (starts[right] <= absdec)
					left = right;
				assert starts[left] <= absdec && (left == starts.length - 1 || absdec < starts[left + 1]) : " " + starts[left] + " " + absdec;
				int gap = absdec - starts[left], dvs = slices[left][1];
				this.x = slices[left][3] + gap / dvs;
				this.a = gap % dvs;
				assert positiveDecisionFor(x, a) == Math.abs(decision) : " " + positiveDecisionFor(x, a) + " " + Math.abs(decision);
				return this;
			}
		}
	}

	/**********************************************************************************************
	 * Decisions recorded during search
	 *********************************************************************************************/

	/**
	 * The set of current decisions.
	 */
	public final SetDense set;

	/**
	 * Structure that permits to associate a bit with any position (of a decision) in the store
	 */
	private final byte[] failedAssignments;

	/**
	 * The encoder/decoder used to represent decisions under the form of integers.
	 */
	public final Decoder decoder;

	/**
	 * Builds the store of decisions for the specified solver
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public Decisions(Solver solver) {
		int decoderNum = solver.head.control.solving.decoder;
		if (decoderNum == 0) { // automatic
			boolean dec1 = (int) ceil(log(solver.problem.variables.length) / log(2)) + (int) ceil(log(solver.problem.features.maxDomSize()) / log(2)) < 31;
			this.decoder = dec1 ? new Decoder1(solver) : new Decoder2(solver);
		} else
			this.decoder = decoderNum == 1 ? new Decoder1(solver) : new Decoder2(solver);

		int nValues = Variable.nInitPracticalValuesFor(solver.problem.variables);
		this.set = new SetDense(nValues);
		this.failedAssignments = new byte[nValues / 8 + 1];
	}

	/**
	 * Returns the variable involved in the last taken decision if the type of this decision is the value of the specified Boolean, null otherwise.
	 */
	public Variable varOfLastDecisionIf(boolean positive) {
		if (set.limit == 0 || (set.last() >= 0) != positive)
			return null;
		return decoder.varIn(set.last());
	}

	// /**
	// * Returns the index of the value involved in the last taken decision, -1 if no decision is present.
	// */
	// public int idxOfLastDecision() {
	// return set.limit >= 0 ? idxIn(set.last()) : -1;
	// }

	/**
	 * Returns true if the last but one decision was negative
	 */
	public boolean isLastButOneNegative() {
		return set.limit >= 1 && set.dense[set.limit - 1] < 0;
	}

	/**
	 * Returns true if the ith stored decision corresponds to a failed assignment (i.e., a positive decision leading directly to a conflict when propagating)
	 * 
	 * @param i
	 *            the position of a decision in the store
	 * @return true if the ith stored decision corresponds to a failed assignment
	 */
	public boolean isFailedAssignment(int i) {
		assert i < set.size();
		return Bit.isAt1(failedAssignments, i);
	}

	/**
	 * Adds a negative decision x!=a to the current store
	 * 
	 * @param x
	 *            the variable involved in the decision
	 * @param a
	 *            the index (of value) involved in the decision
	 */
	public void addNegativeDecision(Variable x, int a) {
		set.add(decoder.negativeDecisionFor(x.num, a));
		assert controlDecisions();
	}

	/**
	 * Returns the depth (actually, position) of the first negative decision in the current store, or -1
	 */
	public int minDepth() {
		int[] dense = set.dense;
		int limit = set.limit;
		for (int i = 0; i <= limit; i++)
			if (dense[i] < 0)
				return i;
		return -1;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append(set.size()).append(" decisions : ");
		for (int i = 0; i < set.size(); i++)
			sb.append(decoder.stringOf(set.dense[i])).append(isFailedAssignment(i) ? " x" : "").append("  ");
		return sb.toString();
	}

	private boolean controlDecisions() {
		return IntStream.range(0, set.size()).allMatch(
				i -> set.dense[i] != 0 && IntStream.range(i + 1, set.size()).allMatch(j -> set.dense[i] != set.dense[j] && set.dense[i] != -set.dense[j]));
	}
}