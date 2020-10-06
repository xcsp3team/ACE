/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problem;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.w3c.dom.Document;

import constraints.Constraint;
import utility.Kit;
import variables.Variable;

public final class Subproblem {
	public final Problem pb;

	private final boolean[] presentVars; // if null, all variables are assumed to be present
	private final boolean[] presentCtrs; // if null, all constraints are assumed to be present

	public boolean isPresentVar(int i) {
		return presentVars == null || presentVars[i];
	}

	public boolean isPresentCtr(int i) {
		return presentCtrs == null || presentCtrs[i];
	}

	public int nPresentVars() {
		return presentVars == null ? pb.variables.length : Kit.countIn(true, presentVars);
	}

	public int nPresentCtrs() {
		return presentCtrs == null ? pb.constraints.length : Kit.countIn(true, presentCtrs);
	}

	public boolean isFullProblem() {
		return nPresentVars() == pb.variables.length && nPresentCtrs() == pb.constraints.length;
	}

	private static boolean[] buildPresentConstraintsFrom(Problem pb, boolean[] presentVars, boolean removeDisconnectedVars) {
		boolean[] presentCtrs = new boolean[pb.constraints.length];
		boolean[] connectedVars = removeDisconnectedVars ? new boolean[presentVars.length] : null;
		for (int i = 0; i < presentCtrs.length; i++) {
			presentCtrs[i] = !Constraint.isInvolvingAbsentVar(pb.constraints[i], presentVars);
			if (removeDisconnectedVars && presentCtrs[i])
				for (Variable x : pb.constraints[i].scp)
					connectedVars[x.num] = true;
		}
		if (removeDisconnectedVars)
			Kit.and(presentVars, connectedVars);
		return presentCtrs;
	}

	private static boolean[] buildPresentVariablesFrom(Problem pb, boolean[] presentCtrs) {
		return Kit.toPrimitive(Stream.of(pb.variables).map(x -> Variable.isInducedBy(x, presentCtrs)));
	}

	public Subproblem(Problem pb, boolean[] presentVars, boolean[] presentCtrs) {
		this.pb = pb;
		this.presentVars = presentVars;
		this.presentCtrs = presentCtrs;
		assert controlCoherence();
	}

	public Subproblem(Problem pb, boolean[] presentVars, boolean removeDisconnectedVars) {
		this(pb, presentVars, buildPresentConstraintsFrom(pb, presentVars, removeDisconnectedVars));
	}

	public Subproblem(Problem pb, boolean[] presentCtrs) {
		this(pb, buildPresentVariablesFrom(pb, presentCtrs), presentCtrs);
	}

	public Subproblem(Problem pb) {
		this(pb, null, null);
	}

	public Document documentXCSP() {
		return new Compiler3Abscon(this).buildDocument();
	}

	private boolean controlCoherence() {
		if (presentVars == null && presentCtrs == null)
			return true;
		if (presentVars == null || presentCtrs == null)
			return false;
		if (pb.variables.length != presentVars.length || pb.constraints.length != presentCtrs.length)
			return false;
		IntStream.range(0, presentCtrs.length).forEach(i -> Kit.control(!presentCtrs[i] || !Constraint.isInvolvingAbsentVar(pb.constraints[i], presentVars),
				() -> "constraint " + pb.constraints[i] + " involving one absent variable "));
		IntStream.range(0, presentVars.length).forEach(i -> Kit.control(!presentVars[i] || !Variable.isInducedBy(pb.variables[i], presentCtrs),
				() -> "variable " + pb.variables[i] + " involving in no present constraint"));
		return true;
	}
}