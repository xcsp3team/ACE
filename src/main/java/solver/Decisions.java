/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package solver;

import java.util.stream.IntStream;

import sets.SetDense;
import utility.Bit;
import utility.Kit;
import variables.Variable;

public final class Decisions {

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

	final Solver solver;

	/**
	 * The set of current decisions.
	 */
	public final SetDense set;

	private final byte[] failedAssignments;

	private final Variable[] variables; // redundant field

	public void reset() {
		set.clear();
	}

	public boolean isFailedAssignment(int i) {
		assert i < set.size();
		return Bit.isAt1(failedAssignments, i);
	}

	public Decisions(Solver solver) {
		this.solver = solver;
		int n1 = (int) Math.ceil(Math.log(solver.problem.variables.length) / Math.log(2));
		int n2 = (int) Math.ceil(Math.log(solver.problem.features.maxDomSize()) / Math.log(2));
		// System.out.println(n1 + " vvs " + n2);
		Kit.control(n1 + n2 < 31, () -> "Cannot represent decisions " + n1 + " " + n2);
		this.OFFSET = (int) Math.pow(2, n2 + 1); // +1 because 0 excluded ???
		int nValues = Variable.nInitValuesFor(solver.problem.variables);
		this.set = new SetDense(nValues);
		this.failedAssignments = new byte[nValues / 8 + 1];
		this.variables = solver.problem.variables;
	}

	/**
	 * Returns the variable involved in the last taken decision if the type of this decision is the value of the specified Boolean, null otherwise.
	 */
	public Variable varOfLastDecisionIf(boolean positive) {
		return set.limit >= 0 && (set.last() >= 0) == positive ? varIn(set.last()) : null;
	}

	public boolean isLastButOneNegative() {
		return set.limit >= 1 && set.dense[set.limit - 1] < 0;
	}

	public void addPositiveDecision(Variable x, int a) {
		set.add(positiveDecisionFor(x.num, a));
		Bit.setTo0(failedAssignments, set.limit);
		assert controlDecisions();
	}

	public void addNegativeDecision(Variable x, int a) {
		set.add(negativeDecisionFor(x.num, a));
		assert controlDecisions();
	}

	public void delPositiveDecision(Variable x) {
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

	public int minDepth() {
		int[] dense = set.dense;
		int limit = set.limit;
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
		StringBuilder sb = new StringBuilder().append(set.size()).append(" decisions : ");
		for (int i = 0; i < set.size(); i++)
			sb.append(stringOf(set.dense[i])).append(isFailedAssignment(i) ? " x" : "").append("  ");
		return sb.toString();
	}

	private boolean controlDecisions() {
		return IntStream.range(0, set.size()).allMatch(i -> set.dense[i] != 0 && IntStream.range(i + 1, set.size())
				.allMatch(j -> set.dense[i] != set.dense[j] && set.dense[i] != -set.dense[j]));
	}
}