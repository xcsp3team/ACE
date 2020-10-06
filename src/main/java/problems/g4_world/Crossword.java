/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

import utility.Kit;

public class Crossword implements ProblemAPI {

	int[][] spots;
	String dictFileName;

	private Map<Integer, List<int[]>> loadWords() {
		Map<Integer, List<int[]>> words = new HashMap<>();
		readFileLines(dictFileName).forEach(w -> words.computeIfAbsent(w.length(), k -> new ArrayList<>()).add(Utilities.wordAsIntArray(w)));
		return words;
	}

	class Hole {
		int row, col, size;
		boolean horizontal;

		Hole(int row, int col, int size, boolean horizontal) {
			this.row = horizontal ? row : col;
			this.col = horizontal ? col : row;
			this.size = size;
			this.horizontal = horizontal;
		}

		Var[] scope(Var[][] x) {
			return variablesFrom(range(size), i -> horizontal ? x[row][col + i] : x[row + i][col]);
		}

		int[] offsetWith(Hole other) {
			if (this.horizontal == other.horizontal)
				return null;
			int[] offset = new int[2];
			if (this.horizontal) {
				offset[0] = other.col - this.col;
				if (offset[0] < 0 || offset[0] > this.size - 1)
					return null;
				offset[1] = this.row - other.row;
				if (offset[1] < 0 || offset[1] > other.size - 1)
					return null;
			} else {
				offset[0] = this.col - other.col;
				if (offset[0] < 0 || offset[0] > other.size - 1)
					return null;
				offset[1] = other.row - this.row;
				if (offset[1] < 0 || offset[1] > this.size - 1)
					return null;
			}
			return offset;
		}

		@Override
		public String toString() {
			return "(" + row + " " + col + " " + size + " " + horizontal + ")";
		}
	}

	private List<Hole> findHoles(int[][] t, boolean untransposed) {
		int nRows = t.length, nCols = t[0].length;
		List<Hole> list = new ArrayList<>();
		for (int i = 0; i < nRows; i++) {
			int start = -1;
			for (int j = 0; j < nCols; j++)
				if (t[i][j] == 1) {
					if (start != -1 && j - start >= 2)
						list.add(new Hole(i, start, j - start, untransposed));
					start = -1;
				} else {
					if (start == -1)
						start = j;
					else if (j == nCols - 1 && nCols - start >= 2)
						list.add(new Hole(i, start, nCols - start, untransposed));
				}
		}
		return list;
	}

	private Hole[] findHoles() {
		List<Hole> list = findHoles(spots, true);
		list.addAll(findHoles(transpose(spots), false));
		return list.toArray(new Hole[0]);
	}

	private Table compatibleWords(Map<Integer, List<int[]>> words, Hole hole1, Hole hole2) {
		int[] offset = hole1.offsetWith(hole2);
		List<int[]> words1 = words.get(hole1.size), words2 = words.get(hole2.size);
		return table().addFrom(range(words1.size()).range(words2.size()),
				(i1, i2) -> words1.get(i1)[offset[0]] == words2.get(i2)[offset[1]] ? tuple(i1, i2) : null);
	}

	@Override
	public void model() {
		Map<Integer, List<int[]>> words = loadWords();
		Hole[] holes = findHoles();
		System.out.println("Holes=" + Kit.join(holes));
		int nRows = spots.length, nCols = spots[0].length, nHoles = holes.length;

		if (modelVariant("")) {
			Var[][] x = array("x", size(nRows, nCols), (i, j) -> dom(range(26)).when(spots[i][j] == 0),
					"x[i][j] is the letter, number from 0 to 25, at row i and column j (when no spot)");

			int[] arities = Stream.of(holes).mapToInt(h -> h.size).sorted().distinct().toArray();
			System.out.println("ARITIES " + Kit.join(arities));
			Var[][] scopes = Stream.of(holes).map(h -> h.scope(x)).toArray(Var[][]::new);

			forall(range(nHoles), i -> extension(scopes[i], words.get(scopes[i].length))).note("fill the grid with words");

			forall(range(arities.length), i -> allDifferentList(Stream.of(scopes).filter(s -> s.length == arities[i]).toArray(Var[][]::new)))
					.tag("distinct-words");
		}
		if (modelVariant("alt")) {
			Var[] w = array("w", size(nHoles), i -> dom(range(words.get(holes[i].size).size())), "w[i] is the ith word to be put in the grid");
			forall(range(nHoles).range(nHoles), (i, j) -> {
				if (i < j && holes[i].offsetWith(holes[j]) != null) {
					extension(vars(w[i], w[j]), compatibleWords(words, holes[i], holes[j]));
				}
			}).note("words must intersect correctly");
			forall(range(nHoles).range(nHoles), (i, j) -> {
				if (i < j && holes[i].size == holes[j].size)
					different(w[i], w[j]);
			}).tag("distinct-words");
		}
	}

}
