/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.todo;

import java.util.Set;
import java.util.TreeSet;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

import utility.Kit;

// class for testing if generation redundant table constraints for subsquare 3*3 could be relevant/efficient
// it seems that the number of tuples is very/too high
public class CrosswordRomanianTestRedundantTables implements ProblemAPI {

	private static final int N_LETTERS = 26;

	private static Stream<String> oneLetterWords() {
		return IntStream.range(0, N_LETTERS).mapToObj(i -> (char) (i + 97) + "");
	}

	private static Stream<String> twoLetterWords() {
		return IntStream.range(0, N_LETTERS).mapToObj(i -> IntStream.range(0, N_LETTERS).mapToObj(j -> ((char) (i + 97) + "" + (char) (j + 97))))
				.flatMap(s -> s);
	}

	private int[][] threeLetterSequences() {
		Set<int[]> set = new TreeSet<>(Kit.lexComparatorGeneral);
		for (int i = 0; i < N_LETTERS; i++) {
			set.add(tuple(N_LETTERS, i, N_LETTERS));
			for (int j = 0; j < N_LETTERS; j++) {
				set.add(tuple(N_LETTERS, i, j));
				set.add(tuple(i, N_LETTERS, j));
				set.add(tuple(i, j, N_LETTERS));
			}
		}
		for (String s : words)
			for (int i = 0; i + 2 < s.length(); i++)
				set.add(IntStream.range(i, i + 3).map(j -> s.charAt(j) - 97).toArray());
		int[][] t = set.stream().distinct().toArray(int[][]::new);
		System.out.println(t.length);
		Stream.of(t).map(tt -> (char) (tt[0] + 97) + "" + (char) (tt[1] + 97) + (char) (tt[2] + 97)).forEach(s -> System.out.print(s + " "));
		return t;
	}

	int n;
	int nMaxWords;
	int wordSizeLimit;

	String mainDict;
	String thematicDict;

	@NotData
	String[] words; // two dictionaries merged

	@Override
	public void model() {
		words = Stream.concat(Stream.concat(oneLetterWords(), twoLetterWords()), Stream.concat(readFileLines(mainDict), readFileLines(thematicDict)))
				.filter(w -> w.length() <= (wordSizeLimit == -1 ? n : wordSizeLimit)).distinct().sorted().toArray(String[]::new);
		int[][] table = threeLetterSequences();

		Var[][] x = array("x", size(3, 3), dom(range(N_LETTERS + 1)), "x[i][j] is the (number of) letter at row i and col j; 26 stands for a black point");
		forall(range(3), i -> extension(x[i], table));
		forall(range(3), j -> extension(columnOf(x, j), table));

		allDifferentList(x[0], x[1], x[2], columnOf(x, 0), columnOf(x, 1), columnOf(x, 2));
	}

}
