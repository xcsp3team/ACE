/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

public class CrosswordDesign1 implements ProblemAPI {

	private static final int N_LETTERS = 26;

	private static Stream<String> oneLetterWords() {
		return IntStream.range(0, N_LETTERS).mapToObj(i -> (char) (i + 97) + "");
	}

	private static Stream<String> twoLetterWords() {
		return IntStream.range(0, N_LETTERS).mapToObj(i -> IntStream.range(0, N_LETTERS).mapToObj(j -> ((char) (i + 97) + "" + (char) (j + 97))))
				.flatMap(s -> s);
	}

	int n;
	int nMaxWords;
	int wordSizeLimit;

	String mainDict, thematicDict;

	@NotData
	Map<Integer, List<int[]>> wordsPerLength; // words of the two merged dictionaries, per length

	@NotData
	Map<Integer, int[]> wordsPointsPerLength;

	private int[] transform(String w) {
		return IntStream.range(0, w.length()).map(j -> w.charAt(j) - (Character.isUpperCase(w.charAt(j)) ? 'A' : 'a')).toArray();
	}

	private void loadWords() {
		String[] words = Stream.concat(Stream.concat(oneLetterWords(), twoLetterWords()), Stream.concat(readFileLines(mainDict), readFileLines(thematicDict)))
				.filter(w -> w.length() <= (wordSizeLimit == -1 ? n : wordSizeLimit)).distinct().sorted().toArray(String[]::new);

		Map<Integer, List<String>> wordsPerLengthII = Stream.of(words).collect(Collectors.groupingBy(s -> s.length()));
		wordsPerLength = new HashMap<>();
		wordsPerLengthII.entrySet().stream()
				.forEach(e -> wordsPerLength.put(e.getKey(), e.getValue().stream().map(s -> transform(s)).collect(Collectors.toList())));

		wordsPointsPerLength = new HashMap<>();
		wordsPerLength.entrySet().stream().forEach(entry -> wordsPointsPerLength.put(entry.getKey(), new int[entry.getValue().size()]));
		readFileLines(thematicDict).forEach(w -> {
			List<String> l = wordsPerLengthII.get(w.length());
			if (l != null) {
				int pos = l.indexOf(w);
				Utilities.control(pos >= 0, "pb");
				wordsPointsPerLength.get(w.length())[pos] = w.length();
			}
		});
		// wordsPerLength.keySet().stream().forEach(i -> System.out.println(i + " : " + Utilities.join(wordsPerLength.get(i))));
		// wordsPointsPerLength.keySet().stream().forEach(i -> System.out.println(i + " : " + Utilities.join(wordsPointsPerLength.get(i))));
	}

	private int nMaxWordsOfLength(int l) {
		int nWordsPerLine = (n + 1) / (l + 1);
		return 2 * n * nWordsPerLine;
	}

	private int[] validCellsForStartingWordOfSize(int l, boolean horizontal) {
		return valuesFrom(range(n).range(n - l + 1), (i, j) -> horizontal ? i * n + j : j * n + i);
	}

	private Table tableFor(int l, int k, boolean horizontal) {
		Table table = table();
		table.add(range(n * n + 4).map(j -> j < 2 ? -1 : j == 2 || j == 3 ? 0 : STAR));
		List<int[]> words = wordsPerLength.get(l);
		for (int p = 0; p < words.size(); p++)
			for (int q : validCellsForStartingWordOfSize(l, horizontal)) {
				int[] t = IntStream.generate(() -> STAR).limit(n * n + 4).toArray();
				t[0] = p;
				t[1] = q;
				t[2] = wordsPointsPerLength.get(l)[p];
				t[3] = l;
				int i = q / n, j = q % n;
				int[] word = words.get(p);
				if (horizontal) {
					if (j > 0) // BP in (i,j-1)
						t[4 + i * n + j - 1] = 26;
					for (int r = 0; r < word.length; r++)
						t[4 + i * n + j + r] = word[r];
					if (j + word.length < n) // BP in (i,j+word.length)
						t[4 + i * n + j + word.length] = 26;
				} else {
					if (i > 0) // BP in (i-1,j)
						t[4 + (i - 1) * n + j] = 26;
					for (int r = 0; r < word.length; r++)
						t[4 + (i + r) * n + j] = word[r];
					if (i + word.length < n) // BP in (i+word.lengt,j)
						t[4 + (i + word.length) * n + j] = 26;
				}
				table.add(t);
			}
		return table;
	}

	@Override
	public void model() {
		loadWords();

		// for (int i = 1; i <= 10; i++)
		// System.out.println("i=" + i + " " + Utilities.join(validCellsForStartingWordOfSize(i, true)) + " "
		// + Utilities.join(validCellsForStartingWordOfSize(i, false)));

		nMaxWords = nMaxWords == -1 ? (n + 1) / 2 : nMaxWords;

		Var[][] x = array("x", size(n, n), dom(range(N_LETTERS + 1)), "x[i][j] is the (number of) letter at row i and col j; 26 stands for a black point");

		Var[][] wh = array("wh", size(n + 1, nMaxWordsOfLength(1)),
				(l, k) -> l > 0 && k < nMaxWordsOfLength(l) ? dom(range(-1, wordsPerLength.get(l).size())) : null,
				"wh[l][k] is the (index of the) kth horizontal word of length l in the grid; -1 means 'no word'");
		Var[][] wv = array("wv", size(n + 1, nMaxWordsOfLength(1)),
				(l, k) -> l > 0 && k < nMaxWordsOfLength(l) ? dom(range(-1, wordsPerLength.get(l).size())) : null,
				"wv[l][k] is the (index of the) kth vertical word of length l in the grid; -1 means 'no word'");

		Var[][] ph = array("ph", size(n + 1, nMaxWordsOfLength(1)),
				(l, k) -> l > 0 && k < nMaxWordsOfLength(l) ? dom(-1, validCellsForStartingWordOfSize(l, true)) : null,
				"ph[l][k] is the position of the (cell index of the) kth horizontal word of length l in the grid; -1 means 'no word'");

		Var[][] pv = array("pv", size(n + 1, nMaxWordsOfLength(1)),
				(l, k) -> l > 0 && k < nMaxWordsOfLength(l) ? dom(-1, validCellsForStartingWordOfSize(l, false)) : null,
				"pv[l][k] is the position of the (cell index of the) kth vertical word of length l in the grid; -1 means 'no word'");

		Var[][] bh = array("bh", size(n + 1, nMaxWordsOfLength(1)), (i, k) -> i > 0 && k < nMaxWordsOfLength(i) ? dom(0, i) : null,
				"bh[l][k] is the benefit of the kth horizontal word of length l in the grid; 0 when 'no word'");

		Var[][] bv = array("bv", size(n + 1, nMaxWordsOfLength(1)), (i, k) -> i > 0 && k < nMaxWordsOfLength(i) ? dom(0, i) : null,
				"bv[l][k] is the benefit of the kth vertical word of length l in the grid; 0 when 'no word'");

		Var[][] lh = array("lh", size(n + 1, nMaxWordsOfLength(1)), (i, k) -> i > 0 && k < nMaxWordsOfLength(i) ? dom(0, i) : null,
				"lh[l][k] is the length of the kth horizontal word of length l in the grid; 0 when 'no word'");

		Var[][] lv = array("lv", size(n + 1, nMaxWordsOfLength(1)), (i, k) -> i > 0 && k < nMaxWordsOfLength(i) ? dom(0, i) : null,
				"lv[l][k] is the length of the kth vertical word of length l in the grid; 0 when 'no word'");

		Var bp = var("bp", dom(range(n * 2 + 1)), "bp is the number of black points in the grid");

		forall(range(n + 1).range(nMaxWordsOfLength(1)), (l, k) -> {
			if (l > 0 && k < nMaxWordsOfLength(l) - 1) {
				implication(eq(wh[l][k], -1), eq(wh[l][k + 1], -1));
				implication(eq(wv[l][k], -1), eq(wv[l][k + 1], -1));
			}
		});

		// forall(range(n + 1).range(nMaxWordsOfLength(1)), (l, k) -> {
		// if (l > 0 && k < nMaxWordsOfLength(l)) {
		// intension(imp(eq(wh[l][k], -1), eq(ph[l][k], -1)));
		// intension(imp(eq(wv[l][k], -1), eq(pv[l][k], -1)));
		// }
		// });
		// forall(range(n + 1).range(nMaxWordsOfLength(1)), (l, k) -> {
		// if (l > 0 && k < nMaxWordsOfLength(l)) {
		// intension(imp(eq(wh[l][k], -1), eq(bh[l][k], 0)));
		// intension(imp(eq(wv[l][k], -1), eq(bv[l][k], 0)));
		// }
		// });

		forall(range(n + 1).range(nMaxWordsOfLength(1)), (l, k) -> {
			if (l > 0 && k < nMaxWordsOfLength(l)) {
				// System.out.println("Table =" + tableFor(l, k, true));
				extension(vars(wh[l][k], ph[l][k], bh[l][k], lh[l][k], x), tableFor(l, k, true));
			}
		});

		forall(range(n + 1).range(nMaxWordsOfLength(1)), (l, k) -> {
			if (l > 0 && k < nMaxWordsOfLength(l)) {
				// System.out.println("Table =" + tableFor(l, k, true));
				extension(vars(wv[l][k], pv[l][k], bv[l][k], lv[l][k], x), tableFor(l, k, false));
			}
		});

		// allDifferentExcept(vars(r, c), tuple(-1, oneLetterPositions));

		allDifferent(vars(ph), exceptValue(-1));
		allDifferent(vars(pv), exceptValue(-1));

		exactly(vars(x), 26, bp);
		sum(vars(bp, lh), EQ, n * n);
		sum(vars(bp, lv), EQ, n * n);

		forall(range(n + 1), l -> {
			if (l > 0) {
				decreasing(clean(wh[l]));
				decreasing(clean(wv[l]));
			}
		});

		forall(range(n).range(n), (i, j) -> {
			if (j < n - 1)
				implication(eq(x[i][j], 26), ne(x[i][j + 1], 26));
			if (i < n - 1)
				implication(eq(x[i][j], 26), ne(x[i + 1][j], 26));
		});

		// atMost(vars(x), 26, n * 2);
		maximize(SUM, vars(bh, bv));

		// decisionVariables(vars(r, c));
	}

	// 1/ optimizer le domaine des variables b - minor
	// 2/ closures - add nogoods
	// 3/ words of the same family - add constraints atMost

}
