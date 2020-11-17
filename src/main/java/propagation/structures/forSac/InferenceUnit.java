/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.structures.forSac;

import java.util.stream.Collectors;
import java.util.stream.IntStream;

import variables.Domain;

public final class InferenceUnit {

	/**
	 * Stores the state of values. If absents[a] is true that means that the value at index a is considered as deleted.
	 */
	public boolean[] absents;

	public boolean modified;

	public InferenceUnit(int size) {
		absents = new boolean[size];
	}

	public void addAbsent(int a) {
		assert !absents[a];
		absents[a] = true;
		modified = true;
	}

	// public void clear(int num1, int a, int num2) {
	// if (num1 != num2) {
	// Arrays.fill(absents, false);
	// modified = false;
	// } else {
	// Arrays.fill(absents, true);
	// absents[a] = false;
	// modified = true;
	// }
	// }

	public void copy(Domain dom) {
		assert dom.initSize() == absents.length;
		for (int i = 0; i < absents.length; i++)
			absents[i] = !dom.isPresent(i);
		modified = false;
	}

	@Override
	public String toString() {
		return " elements = {" + IntStream.range(0, absents.length).filter(i -> absents[i]).mapToObj(i -> i + " ").collect(Collectors.joining()) + "}";
	}
}