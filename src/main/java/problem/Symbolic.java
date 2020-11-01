/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problem;

import java.util.HashMap;
import java.util.Map;

import org.xcsp.common.Constants;

import constraints.Constraint;

public final class Symbolic {

	public static String[] replaceSymbols(Symbolic symbolic, String[] t) {
		return symbolic == null ? t : symbolic.replaceSymbols(t);
	}

	public final Map<String, Integer> mapOfSymbols = new HashMap<>();

	public final Map<Constraint, String[][]> mapOfTuples = new HashMap<>();

	public int[] manageSymbols(String[] symbols) {
		int[] t = new int[symbols.length];
		for (int i = 0; i < t.length; i++) {
			assert !symbols[i].equals(Constants.STAR_SYMBOL);
			t[i] = mapOfSymbols.computeIfAbsent(symbols[i], k -> mapOfSymbols.size());
		}
		return t;
	}

	public String[] replaceSymbols(String[] tokens) {
		String[] t = new String[tokens.length];
		for (int i = 0; i < t.length; i++) {
			Integer v = mapOfSymbols.get(tokens[i]);
			t[i] = v != null ? v.toString() : tokens[i];
		}
		return t;
	}

	public int[][] replaceSymbols(String[][] tuples) {
		int[][] m = new int[tuples.length][];
		for (int i = 0; i < m.length; i++) {
			m[i] = new int[tuples[i].length];
			for (int j = 0; j < m[i].length; j++) {
				Integer v = mapOfSymbols.get(tuples[i][j]);
				m[i][j] = v != null ? v : tuples[i][j].equals(Constants.STAR_SYMBOL) ? Constants.STAR : Integer.parseInt(tuples[i][j]);
			}
		}
		return m;
	}

	public void store(Constraint c, String[][] m) {
		mapOfTuples.put(c, m);
	}

	// public String replaceSymbols(String s) {
	// for (Entry<String, Integer> entry : mapOfSymbols.entrySet())
	// s = s.replaceAll(entry.getKey(), entry.getValue() + "");
	// return s;
	// }
}
