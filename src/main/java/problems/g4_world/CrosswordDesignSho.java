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
import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

public class CrosswordDesignSho implements ProblemAPI {

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
	String[] words; // words of the two merged dictionaries

	@NotData
	int[] wordsPoints;

	@NotData
	int[] oneLetterPositions;

	private void loadWords() {
		words = Stream.concat(Stream.concat(oneLetterWords(), twoLetterWords()), Stream.concat(readFileLines(mainDict), readFileLines(thematicDict)))
				.filter(w -> w.length() <= (wordSizeLimit == -1 ? n : wordSizeLimit)).distinct().sorted().toArray(String[]::new);
		wordsPoints = new int[words.length];
		List<String> list = Arrays.asList(words);
		readFileLines(thematicDict).forEach(w -> {
			int pos = list.indexOf(w);
			if (pos != -1)
				wordsPoints[pos] = w.length(); // thematic words have some value (their lengths)
		});
		oneLetterPositions = oneLetterWords().mapToInt(w -> list.indexOf(w)).toArray();
		// Map<Integer, List<String>> wordsPerLength = Stream.of(words).collect(Collectors.groupingBy(s -> s.length()));
		// wordsPerLength.keySet().stream().forEach(i -> System.out.println(i + " : " + Kit.join(wordsPerLength.get(i))));
	}

	private Table shortTableFor(int k) {
		boolean lastWord = k == nMaxWords - 1;
		List<int[]> list = new ArrayList<>();
		if (k != 0)
			list.add(range(n + 4).map(i -> i == 0 || i == 1 | i == 3 ? -1 : i == 2 ? 0 : Constants.STAR));
		int[] possiblePositions = k == 0 ? new int[] { 0, 1 } : vals(range(2 * k, n));
		for (int p : possiblePositions)
			for (int i = 0; i < words.length; i++) {
				int bp = p + words[i].length(); // position of the black point, just after the word
				if (bp <= n) {
					int[] tuple = new int[n + 4];
					tuple[0] = p;
					tuple[1] = i;
					tuple[2] = wordsPoints[i];
					if (lastWord && bp < n - 1)
						continue;
					tuple[3] = lastWord ? -1 : bp <= n - 2 ? bp + 1 : -1;
					for (int j = 4; j < tuple.length; j++) {
						if (j - 4 == p - 1 || j - 4 == bp)
							tuple[j] = 26; // black points
						else if (p <= j - 4 && j - 4 < p + words[i].length())
							tuple[j] = words[i].charAt(j - 4 - p) - 97;
						else
							tuple[j] = Constants.STAR;
					}
					list.add(tuple);
				}
			}
		return table().add(list);
	}

	@Override
	public void model() {
		loadWords();
		nMaxWords = nMaxWords == -1 ? (n + 1) / 2 : nMaxWords;

		Var[][] x = array("x", size(n, n), dom(range(N_LETTERS + 1)), "x[i][j] is the (number of) letter at row i and col j; 26 stands for a black point");
		Var[][] r = array("r", size(n, nMaxWords), dom(range(-1, words.length)), "r[i][k] is the (index of) kth word at row i; -1 means 'no word'");
		Var[][] c = array("c", size(n, nMaxWords), dom(range(-1, words.length)), "c[j][k] is the (index of) kth word at col j; -1 means 'no word'");
		Var[][] pr = array("pr", size(n, nMaxWords + 1), (i, k) -> k == 0 ? dom(0, 1) : k == nMaxWords ? dom(-1) : dom(range(-1, n)),
				"pr[i][k] is the position (index of col) of the kth word at row i; -1 means 'no position' because 'no word'");
		Var[][] pc = array("pc", size(n, nMaxWords + 1), (j, k) -> k == 0 ? dom(0, 1) : k == nMaxWords ? dom(-1) : dom(range(-1, n)),
				"pc[j][k] is the position (index of row) of the kth word at col j; -1 means 'no position' because 'no word'");
		Var[][] br = array("br", size(n, nMaxWords), dom(range(n + 1)),
				"br[i][k] is the benefit of the kth word at row i; 0 means that the word is either absent or from the full dictionary");
		Var[][] bc = array("bc", size(n, nMaxWords), dom(range(n + 1)),
				"bc[j][k] is the benfit of the kth word at col j; 0 means that the word is either absent or from the full dictionary");

		Table[] tables = IntStream.range(0, nMaxWords).mapToObj(k -> shortTableFor(k)).toArray(Table[]::new);
		forall(range(n).range(nMaxWords), (i, k) -> extension(vars(pr[i][k], r[i][k], br[i][k], pr[i][k + 1], x[i]), tables[k]));
		forall(range(n).range(nMaxWords), (j, k) -> extension(vars(pc[j][k], c[j][k], bc[j][k], pc[j][k + 1], columnOf(x, j)), tables[k]));

		// allDifferentExcept(vars(r, c), tuple(-1, oneLetterPositions));

		atMost(vars(x), 26, n * 2);

		maximize(SUM, vars(br, bc)); // .note("maximizing the summed benefit of words put in the grid");

		// decisionVariables(vars(r, c));
	}

	// 1/ optimizer le domaine des variables b - minor
	// 2/ closures - add nogoods
	// 3/ words of the same family - add constraints atMost

}
