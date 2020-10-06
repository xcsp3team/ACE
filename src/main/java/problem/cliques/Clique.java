/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package problem.cliques;

import constraints.Constraint;
import utility.Kit;
import variables.Variable;

/**
 * The class representing a 3 clique.
 * 
 */
public class Clique implements Comparable<Clique> {
	/**
	 * The binary constraint involving x and y.
	 */
	public final Constraint c1;

	/**
	 * The binary constraint involving y and z.
	 */
	public final Constraint c2;

	/**
	 * The binary constraint involving x and z.
	 */
	public final Constraint c3;

	/**
	 * The variable involved in c1 and c3
	 */
	public final Variable x;

	/**
	 * The variable involved in c1 and c2
	 */
	public final Variable y;

	/**
	 * The variable involved in c2 and c3
	 */
	public final Variable z;

	private int cliquePositionForC1 = -1;

	private int cliquePositionForC2 = -1;

	private int cliquePositionForC3 = -1;

	public Constraint wrk1; // working constraint 1

	public Constraint wrk2;

	public Variable setWorkingSet(Variable firstVar, Variable secondVar) {
		if (x != firstVar && x != secondVar) {
			if (firstVar == y) {
				wrk1 = c1;
				wrk2 = c3;
			} else {
				wrk1 = c3;
				wrk2 = c1;
			}
			return x;
		}
		if (y != firstVar && y != secondVar) {
			if (firstVar == x) {
				wrk1 = c1;
				wrk2 = c2;
			} else {
				wrk1 = c2;
				wrk2 = c1;
			}
			return y;
		}
		if (firstVar == x) {
			wrk1 = c3;
			wrk2 = c2;
		} else {
			wrk1 = c2;
			wrk2 = c3;
		}
		return z;
	}

	public Constraint getEdgeConstraint(Constraint c, Variable w) {
		assert c.involves(w);
		if (c == c1)
			return (w == x ? c3 : c2);
		if (c == c2)
			return (w == y ? c1 : c3);
		return (w == x ? c1 : c2);
	}

	private boolean isInvolving(Constraint c) {
		return c1 == c || c2 == c || c3 == c;
	}

	private Variable getThirdVariableWrt(Constraint c) {
		assert isInvolving(c);
		return c == c1 ? z : c == c2 ? x : y;
	}

	public int compareTo(Clique clique) {
		Constraint c = clique.isInvolving(c1) ? c1 : clique.isInvolving(c2) ? c2 : clique.isInvolving(c3) ? c3 : null;
		return this.getThirdVariableWrt(c).dom.size() - clique.getThirdVariableWrt(c).dom.size();
	}

	public Clique(Constraint c1, Constraint c2, Constraint c3) {
		Kit.control(c1.scp.length == 2 && c2.scp.length == 2 && c3.scp.length == 2);
		this.c1 = c1;
		this.c2 = c2;
		this.c3 = c3;
		x = c3.involves(c1.scp[0]) ? c1.scp[0] : c1.scp[1];
		y = c2.involves(c1.scp[0]) ? c1.scp[0] : c1.scp[1];
		z = c2.involves(c3.scp[0]) ? c3.scp[0] : c3.scp[1];
		Kit.control(controlClique());
	}

	public void setPosition(Constraint c, int position) {
		assert isInvolving(c);
		if (c1 == c)
			cliquePositionForC1 = position;
		else if (c2 == c)
			cliquePositionForC2 = position;
		else
			cliquePositionForC3 = position;
	}

	public int getPositionOf(Constraint c) {
		assert isInvolving(c);
		return c1 == c ? cliquePositionForC1 : c2 == c ? cliquePositionForC2 : cliquePositionForC3;
	}

	public String toString() {
		return "(" + c1 + "," + c2 + "," + c3 + ")";
	}

	private boolean controlClique() {
		return x != y && x != z && y != z && c1.involves(x) && c1.involves(y) && c2.involves(y) && c2.involves(z) && c3.involves(x) && c3.involves(z);
	}
}
