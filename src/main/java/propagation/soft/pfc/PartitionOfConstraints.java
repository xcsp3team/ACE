/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.soft.pfc;

import java.util.Arrays;

import constraints.Constraint;
import search.Solver;
import utility.Kit;
import utility.operations.Calculator;
import variables.Variable;

public abstract class PartitionOfConstraints {

	protected Solver solver;

	protected Constraint[] ctrs;

	/** The cost of all covered constraints (for example, the number of past constraints that are violated for MaxCSP) */
	protected long distance;

	/** membership[c] is the variable x whose part contains c (or -1 if past constraint, i.e. a constraint with only past variables) */
	public int[] membership;

	/** first[x] is the first constraint c belonging to the part of x */
	protected int[] first;

	/** next[c] is the next constraint belonging to the same part */
	protected int[] next;

	/** size[x] is the size of the part of x */
	protected int[] size;

	/** first of past constraints */
	protected int firstPast;

	protected PartitionOfConstraints(Solver solver) {
		this.solver = solver;
		this.ctrs = solver.pb.constraints;
		this.membership = new int[solver.pb.constraints.length];
		this.next = new int[solver.pb.constraints.length];
		this.first = new int[solver.pb.variables.length];
		this.size = new int[solver.pb.variables.length];
	}

	protected void dealWithPastConstraint(Constraint c) {
		membership[c.num] = -1; // because past constraint (i.e. constraint covered by the current solver instantiation)
		next[c.num] = firstPast;
		firstPast = c.num;
		distance = Calculator.add(distance, c.costOfCurrInstantiation());
	}

	protected abstract double evaluate(Constraint c, Variable x, boolean incremental);

	protected final void dealWithFutureConstraint(Constraint c, boolean incremental) {
		int xnum = -1;
		double bestEval = -1;
		for (Variable x : c.scp) {
			if (x.isAssigned())
				continue;
			double eval = evaluate(c, x, incremental);
			if (eval > bestEval) { // || eval == bestEval && c.vapOf(x) < c.vapOf(solver.problem.variables[bestVar]))
				xnum = x.num;
				bestEval = eval;
			}
		}
		assert xnum != -1;
		membership[c.num] = xnum;
		next[c.num] = first[xnum];
		first[xnum] = c.num;
		size[xnum]++;
	}

	public final void totalInit() {
		Arrays.fill(first, -1);
		Arrays.fill(size, 0);
		firstPast = -1;
		distance = solver.rs.cp.settingOptimization.lowerBound;
		for (Constraint ctr : ctrs)
			if (ctr.futvars.size() == 0)
				dealWithPastConstraint(ctr);
			else
				dealWithFutureConstraint(ctr, false);
		// displayPartition();
		assert controlPartition();
	}

	protected abstract void updateStructures(Constraint c, Variable x);

	protected void incrementalInit() {
		Variable x = solver.futVars.lastPast();
		for (Constraint c : x.ctrs)
			if (c.futvars.size() == 0)
				dealWithPastConstraint(c);
			else if (membership[c.num] == x.num)
				dealWithFutureConstraint(c, true);
			else
				for (int i = c.futvars.limit; i >= 0; i--)
					updateStructures(c, c.scp[c.futvars.dense[i]]);
		first[x.num] = -1;
		assert controlPartition();
	}

	public void init(boolean incremental) {
		if (incremental)
			incrementalInit();
		else
			totalInit();
	}

	/**
	 * returns a value equivalent to ic_ia + dac_ia where i is the given variable and a the given index
	 */
	public abstract long computeSumMinCostsOf(Variable x, int a);

	protected boolean controlPartition() {
		for (Variable x : solver.pb.variables)
			for (int cnum = first[x.num]; cnum != -1; cnum = next[cnum])
				Kit.control(membership[cnum] == x.num, () -> "pb with membership");
		for (Constraint c : solver.pb.constraints)
			if (membership[c.num] == -1) {
				Kit.control(c.futvars.size() == 0, () -> "not all assigned in  ");
			} else { // membership[i] is the variable id
				boolean found = false;
				for (int cnum = first[membership[c.num]]; !found && cnum != -1; cnum = next[cnum])
					if (cnum == c.num)
						found = true;
				Kit.control(found, () -> "constraint not found");
			}
		return true;
	}

	protected void displayPartition() {
		for (Variable x : solver.pb.variables) {
			Kit.log.fine(x + " of size " + size[x.num] + " :");
			for (int cnum = first[x.num]; cnum != -1; cnum = next[cnum])
				Kit.log.fine(ctrs[cnum] + " ");
		}
	}
}
