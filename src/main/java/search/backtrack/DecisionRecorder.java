/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search.backtrack;

import java.util.stream.IntStream;

import sets.SetDense;
import utility.Bit;
import utility.Kit;
import variables.Variable;

public final class DecisionRecorder {

	/**********************************************************************************************
	 * Coding/decoding decisions
	 *********************************************************************************************/

	private final int OFFSET;

	public final int positiveDecisionFor(int num, int a) {
		return 1 + a + OFFSET * num;
	}

	public final int negativeDecisionFor(int num, int a) {
		return -(1 + a + OFFSET * num);
	}

	public final int numIn(int dec) {
		return Math.abs(dec) / OFFSET;
	}

	public final Variable varIn(int dec) {
		return variables[Math.abs(dec) / OFFSET];
	}

	public final int idxIn(int dec) {
		return Math.abs(dec) % OFFSET - 1;
	}

	public final int valIn(int dec) {
		return varIn(dec).dom.toVal(idxIn(dec));
	}

	/**********************************************************************************************
	 * Decisions recorded during search
	 *********************************************************************************************/

	SolverBacktrack solver;

	/**
	 * The set of current decisions.
	 */
	public final SetDense decisions;

	private final byte[] failedAssignments;

	private final Variable[] variables; // redundant field

	public void reset() {
		decisions.clear();
	}

	public boolean isFailedAssignment(int i) {
		assert i < decisions.size();
		return Bit.isAt1(failedAssignments, i);
	}

	public DecisionRecorder(SolverBacktrack solver) {
		this.solver = solver;
		int n1 = (int) Math.ceil(Math.log(solver.pb.variables.length) / Math.log(2));
		int n2 = (int) Math.ceil(Math.log(solver.pb.stuff.maxDomSize()) / Math.log(2));
		Kit.control(n1 + n2 <= 32);
		this.OFFSET = (int) Math.pow(2, n2 + 1); // +1 because 0 excluded ???
		int nValues = Variable.nInitValuesFor(solver.pb.variables);
		this.decisions = new SetDense(nValues);
		this.failedAssignments = new byte[nValues / 8 + 1];
		this.variables = solver.pb.variables;
	}

	/**
	 * Returns the variable involved in the last taken decision if the type of this decision is the value of the specified Boolean, null otherwise.
	 */
	public Variable varOfLastDecisionIf(boolean positive) {
		return decisions.limit >= 0 && (decisions.last() >= 0) == positive ? varIn(decisions.last()) : null;
	}

	public boolean isLastButOneDecisionNegative() {
		return decisions.limit >= 1 && decisions.dense[decisions.limit - 1] < 0;
	}

	public void addPositiveDecision(Variable x, int a) {
		decisions.add(positiveDecisionFor(x.num, a));
		Bit.setTo0(failedAssignments, decisions.limit);
		assert controlDecisions();
	}

	public void addNegativeDecision(Variable x, int a) {
		decisions.add(negativeDecisionFor(x.num, a));
		assert controlDecisions();
	}

	public void delPositiveDecision(Variable x) {
		int[] dense = decisions.dense;
		int limit = decisions.limit;
		if (dense[limit] > 0)
			Bit.setTo1(failedAssignments, limit);
		else
			while (dense[limit] < 0)
				limit--; // for discarding the negative decisions that follow the positive decision
		assert dense[limit] > 0 && numIn(dense[limit]) == x.num : toString();
		decisions.limit = limit - 1; // -1 for discarding the positive decision
	}

	public int minDepth() {
		int[] dense = decisions.dense;
		int limit = decisions.limit;
		for (int i = 0; i <= limit; i++)
			if (dense[i] < 0)
				return i;
		return -1;
	}

	public final String stringOf(int dec) {
		assert dec != 0;
		return varIn(dec) + (dec > 0 ? "=" : "!=") + valIn(dec) + (valIn(dec) != idxIn(dec) ? "(" + idxIn(dec) + ")" : "");
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append(decisions.size()).append(" decisions : ");
		for (int i = 0; i < decisions.size(); i++)
			sb.append(stringOf(decisions.dense[i])).append(isFailedAssignment(i) ? " x" : "").append("  ");
		return sb.toString();
	}

	private boolean controlDecisions() {
		return IntStream.range(0, decisions.size()).allMatch(i -> decisions.dense[i] != 0 && IntStream.range(i + 1, decisions.size())
				.allMatch(j -> decisions.dense[i] != decisions.dense[j] && decisions.dense[i] != -decisions.dense[j]));
	}
}