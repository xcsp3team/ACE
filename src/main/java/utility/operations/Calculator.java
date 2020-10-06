/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package utility.operations;

import utility.Kit;

public final class Calculator {

	public static final long add(long left, long right) {
		if (right > 0 ? left > Long.MAX_VALUE - right : left < Long.MIN_VALUE - right)
			Kit.exit("pb overflow " + left + " " + right);
		return left + right;
	}

	public static final long add(long left, long center, long right) {
		return add(add(left, center), right);
	}

	public static final void add(long[] t, int index, long right) {
		long left = t[index];
		if (right > 0 ? left > Long.MAX_VALUE - right : left < Long.MIN_VALUE - right)
			Kit.exit("pb overflow ");
		t[index] += right;
	}

}
