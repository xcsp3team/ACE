/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Transitions;
import org.xcsp.modeler.api.ProblemAPI;

import utility.Kit;

public class Nonogram implements ProblemAPI {

	int[][] rowPatterns, colPatterns;

	private List<int[]> buildTuples(List<int[]> list, int[] t, int i, int[] pattern, int patternFrom) {
		if (i + Kit.sum(pattern, patternFrom) + (pattern.length - 1 - patternFrom) > t.length)
			return list; // because no enough room for remaining patterns
		if (i == t.length)
			list.add(t.clone());
		else {
			t[i] = 0;
			buildTuples(list, t, i + 1, pattern, patternFrom);
			if (patternFrom < pattern.length) {
				for (int j = i; j < i + pattern[patternFrom]; j++)
					t[j] = 1;
				if (i + pattern[patternFrom] == t.length)
					buildTuples(list, t, i + pattern[patternFrom], pattern, patternFrom + 1);
				else {
					t[i + pattern[patternFrom]] = 0;
					buildTuples(list, t, i + pattern[patternFrom] + 1, pattern, patternFrom + 1);
				}
			}
		}
		return list; // for method chaining
	}

	private int[][] tableFor(boolean row, int[] pattern, Map<String, int[][]> cache) {
		String key = (row ? "R" : "C") + Utilities.join(pattern);
		if (!cache.containsKey(key)) {
			List<int[]> tuples = buildTuples(new ArrayList<int[]>(), new int[row ? colPatterns.length : rowPatterns.length], 0, pattern, 0);
			cache.put(key, tuples.stream().sorted(Utilities.lexComparatorInt).toArray(int[][]::new));
		}
		return cache.get(key);
	}

	private Automaton automatonFor(int[] nonogramPattern) {
		Function<Integer, String> q = i -> "q" + i;
		int nStates = 0;
		Transitions transitions = transitions();
		if (nonogramPattern.length == 0) {
			nStates = 1;
			transitions.add(q.apply(0), 0, q.apply(0));
		} else {
			nStates = IntStream.of(nonogramPattern).sum() + nonogramPattern.length;
			int num = 0;
			for (int i = 0; i < nonogramPattern.length; i++) {
				transitions.add(q.apply(num), 0, q.apply(num));
				for (int j = 0; j < nonogramPattern[i]; j++)
					transitions.add(q.apply(num), 1, q.apply(++num));
				if (i < nonogramPattern.length - 1)
					transitions.add(q.apply(num), 0, q.apply(++num));
			}
			transitions.add(q.apply(num), 0, q.apply(num));
		}
		return automaton(q.apply(0), transitions, q.apply(nStates - 1));
	}

	@Override
	public void model() {
		int nRows = rowPatterns.length, nCols = colPatterns.length;

		Var[][] x = array("x", size(nRows, nCols), dom(0, 1), "x[i][j] is 1 iff the cell at row i and col j is colored in black");

		if (modelVariant("")) {
			forall(range(nRows), i -> regular(x[i], automatonFor(rowPatterns[i])));
			forall(range(nCols), j -> regular(columnOf(x, j), automatonFor(colPatterns[j])));
		}
		if (modelVariant("table")) {
			Map<String, int[][]> cache = new HashMap<>();
			forall(range(nRows), i -> extension(x[i], tableFor(true, rowPatterns[i], cache)));
			forall(range(nCols), j -> extension(columnOf(x, j), tableFor(false, colPatterns[j], cache)));
		}

	}
}
