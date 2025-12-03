/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package learning;

import java.util.stream.Stream;

import utility.Bit;
import variables.Variable;

/**
 * An IPS is an Inconsistent Partial State. It is composed of membership decisions and is equivalent to generalized nogoods.
 * 
 * @author Christophe Lecoutre
 */
public final class Ips {

	/**
	 * Variables of the membership decisions of the IPS; vars[i] is the variable of the ith membership decision
	 */
	public final Variable[] vars;

	/**
	 * Sets of the membership decisions of the IPS; doms[i] is the binary representation of the set (domain) of the ith
	 * membership decision (it concerns value indexes)
	 */
	public final long[][] doms;

	/**
	 * The first watched position; vars[watchPos0] is the first watched variable
	 */
	private int watchPos0 = -1;

	/**
	 * The second watched position; vars[watchPos1] is the second watched variable
	 */
	private int watchPos1 = -1;

	/**
	 * The value index for the first watched variable
	 */
	private int watchIdx0 = -1;

	/**
	 * The value index for the second watched variable
	 */
	private int watchIdx1 = -1;

	/**
	 * @return the size of the IPS (i.e., the number of involved membership decisions)
	 */
	public int size() {
		return vars.length;
	}

	public int varNumFor(int watch) {
		return vars[watch == 0 ? watchPos0 : watchPos1].num;
	}

	public int watchPosFor(int watch) {
		return watch == 0 ? watchPos0 : watchPos1;
	}

	public int watchIdxFor(int watch) {
		return watch == 0 ? watchIdx0 : watchIdx1;
	}

	/**
	 * @param x
	 *            a variable
	 * @return true is the specified variable (actually, the membership decision involving it) is currently watched
	 */
	public boolean isWatched(Variable x) {
		return vars[watchPos0] == x || vars[watchPos1] == x;
	}

	/**
	 * @param x
	 *            a variable
	 * @return 0 if x is the first watched variable, 1 otherwise
	 */
	public int watchFor(Variable x) {
		// assert isWatched(x);
		return vars[watchPos0] == x ? 0 : 1;
	}

	public void setIndex(int watchPosition, int a) {
		if (watchPosition == 0)
			watchIdx0 = a;
		else
			watchIdx1 = a;
	}

	public void setWatch(int watch, int pos, int a) {
		if (watch == 0) {
			watchPos0 = pos;
			watchIdx0 = a;
		} else {
			watchPos1 = pos;
			watchIdx1 = a;
		}
	}

	/**
	 * Builds an IPS for the specified recorder while considering the current domains of the specified variables
	 * 
	 * @param reasoner
	 *            the recorder to which this object is attached
	 * @param vars
	 *            the variables of the IPS
	 */
	public Ips(Variable[] vars) {
		this.vars = vars;
		this.doms = Stream.of(vars).map(x -> x.dom.binary().clone()).toArray(long[][]::new);
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof Ips))
			return false;
		Ips ips = (Ips) o;
		if (vars.length != ips.vars.length)
			return false;
		for (int i = 0; i < vars.length; i++)
			if (vars[i] != ips.vars[i])
				return false;
		for (int i = 0; i < doms.length; i++)
			for (int j = 0; j < doms[i].length; j++)
				if (doms[i][j] != ips.doms[i][j])
					return false;
		return true;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("IPS of size " + vars.length + " with watch1 = " + watchPos0 + " and watch2 = " + watchPos1 + "\n");
		for (int i = 0; i < vars.length; i++)
			sb.append(vars[i] + " : " + Bit.decrypt(doms[i]) + " \n");
		return sb.append("end\n").toString();
	}
}
