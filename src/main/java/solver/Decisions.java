/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package solver;

import static utility.Kit.control;

import java.util.stream.IntStream;

import interfaces.Observers.ObserverOnAssignments;
import interfaces.Observers.ObserverOnRuns;
import sets.SetDense;
import utility.Bit;
import variables.Variable;

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
		set.add(positiveDecisionFor(x.num, a));
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
		assert dense[limit] > 0 && numIn(dense[limit]) == x.num : toString();
		set.limit = limit - 1; // -1 for discarding the positive decision
	}

	/**********************************************************************************************
	 * Coding/decoding decisions
	 *********************************************************************************************/

	private final int OFFSET;

	/**
	 * Returns the code for the specified positive decision
	 * 
	 * @param x
	 *            the (number of the) variable involved in the positive decision
	 * @param a
	 *            the index (of value) involved in the positive decision
	 * @return the code for the specified positive decision
	 */
	public final int positiveDecisionFor(int x, int a) {
		return 1 + a + OFFSET * x;
	}

	/**
	 * Returns the code for the specified negative decision
	 * 
	 * @param x
	 *            the (number of the) variable involved in the negative decision
	 * @param a
	 *            the index (of value) involved in the negative decision
	 * @return the code for the specified negative decision
	 */
	public final int negativeDecisionFor(int x, int a) {
		return -(1 + a + OFFSET * x);
	}

	/**
	 * Returns the number of the variable involved in the decision whose code is specified
	 * 
	 * @param dec
	 *            the code of a decision
	 * @return the number of the variable involved in the decision whose code is specified
	 */
	public final int numIn(int dec) {
		return Math.abs(dec) / OFFSET;
	}

	/**
	 * Returns the variable involved in the decision whose code is specified
	 * 
	 * @param dec
	 *            the code of a decision
	 * @return the variable involved in the decision whose code is specified
	 */
	public final Variable varIn(int dec) {
		return variables[Math.abs(dec) / OFFSET];
	}

	/**
	 * Returns the value index involved in the decision whose code is specified
	 * 
	 * @param dec
	 *            the code of a decision
	 * @return the value index involved in the decision whose code is specified
	 */
	public final int idxIn(int dec) {
		return Math.abs(dec) % OFFSET - 1;
	}

	/**
	 * Returns the value corresponding to the index involved in the decision whose code is specified
	 * 
	 * @param dec
	 *            the code of a decision
	 * @return the value corresponding to the index involved in the decision whose code is specified
	 */
	public final int valIn(int dec) {
		return varIn(dec).dom.toVal(idxIn(dec));
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
	 * The variables of the problem (redundant field)
	 */
	private final Variable[] variables;

	/**
	 * Builds the store of decisions for the specified solver
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public Decisions(Solver solver) {
		this.variables = solver.problem.variables;
		int n1 = (int) Math.ceil(Math.log(variables.length) / Math.log(2));
		int n2 = (int) Math.ceil(Math.log(solver.problem.features.maxDomSize()) / Math.log(2));
		// System.out.println(n1 + " vvs " + n2);
		control(n1 + n2 < 31, () -> "Cannot represent decisions " + n1 + " " + n2);
		this.OFFSET = (int) Math.pow(2, n2 + 1); // +1 because 0 excluded ???
		int nValues = Variable.nInitPracticalValuesFor(variables);
		this.set = new SetDense(nValues);
		this.failedAssignments = new byte[nValues / 8 + 1];
	}

	/**
	 * Returns the variable involved in the last taken decision if the type of this decision is the value of the specified Boolean, null otherwise.
	 */
	public Variable varOfLastDecisionIf(boolean positive) {
		return set.limit >= 0 && (set.last() >= 0) == positive ? varIn(set.last()) : null;
	}
	
	/**
	 * Returns the index of the value involved in the last taken decision, -1 if no decision is present.
	 */
	public int idxOfLastDecision() {
		return set.limit >= 0 ? idxIn(set.last()) : -1;
	}

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
		set.add(negativeDecisionFor(x.num, a));
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

	/**
	 * Returns the string representation of the decision whose code is specified
	 * 
	 * @param dec
	 *            the code of a decision
	 * @return the string representation of the decision whose code is specified
	 */
	public final String stringOf(int dec) {
		assert dec != 0;
		return varIn(dec) + (dec > 0 ? "=" : "!=") + valIn(dec);
		// + (valIn(dec) != idxIn(dec) ? "(" + idxIn(dec) + ")" : "");
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append(set.size()).append(" decisions : ");
		for (int i = 0; i < set.size(); i++)
			sb.append(stringOf(set.dense[i])).append(isFailedAssignment(i) ? " x" : "").append("  ");
		return sb.toString();
	}

	private boolean controlDecisions() {
		return IntStream.range(0, set.size()).allMatch(
				i -> set.dense[i] != 0 && IntStream.range(i + 1, set.size()).allMatch(j -> set.dense[i] != set.dense[j] && set.dense[i] != -set.dense[j]));
	}
}