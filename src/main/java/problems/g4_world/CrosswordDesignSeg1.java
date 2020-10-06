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
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

import constraints.hard.extension.CtrExtensionSegmented;
import constraints.hard.extension.structures.SegmentedTuple;
import constraints.hard.extension.structures.SegmentedTuple.RestrictionTable;
import problem.Problem;
import problems.g4_world.CrosswordDesignSeg2.WordPattern;
import variables.Variable;

public class CrosswordDesignSeg1 implements ProblemAPI {

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

	String mainDict;
	String thematicDict;

	@NotData
	String[] words; // two dictionaries merged

	@NotData
	int[] wordsPoints;

	@NotData
	int[][][] wordsWithPoints; // wordsWithPoints[i] gives the words (with points) of length i

	@NotData
	int[] oneLetterPositions;

	// class WordPattern {
	// int start, length;
	//
	// WordPattern(int start, int length) {
	// this.start = start;
	// this.length = length;
	// }
	//
	// int nextStart() {
	// return start + length + 1;
	// }
	// }

	SegmentedTuple buildSpliTuple(List<WordPattern> wordPatterns, Var[] a, Var[] b) {
		int[] prefix = IntStream.range(0, n + nMaxWords).map(i -> Constants.STAR).toArray();
		for (WordPattern wp : wordPatterns) {
			int i = wp.start - 1;
			if (i >= 0)
				prefix[i] = N_LETTERS;
			i = wp.start + wp.length;
			if (i < n)
				prefix[i] = N_LETTERS;
		}
		int nIrrelevantBenefits = b.length - wordPatterns.size();
		for (int i = 0; i < nIrrelevantBenefits; i++)
			prefix[n + nMaxWords - 1 - i] = 0;
		List<RestrictionTable> list = new ArrayList<>();
		for (int k = 0; k < wordPatterns.size(); k++) {
			int kk = k;
			WordPattern wp = wordPatterns.get(k);
			Variable[] subscp = IntStream.rangeClosed(0, wp.length).mapToObj(i -> i < wp.length ? a[wp.start + i] : b[kk]).toArray(Variable[]::new);
			int[][] subtable = wordsWithPoints[wp.length];
			list.add(new RestrictionTable(subscp, subtable));
		}
		return new SegmentedTuple(prefix, list.toArray(new RestrictionTable[0]));
	}

	void buildSpliTuples(List<WordPattern> wordPatterns, List<SegmentedTuple> splitTuples, Var[] a, Var[] b) {
		if (wordPatterns.size() == 0) {
			for (int i = 0; i <= 1; i++) {
				for (int l = 1; l <= n - i; l++) {
					List<WordPattern> wordPatternsCloned = wordPatterns.stream().collect(Collectors.toList());
					wordPatternsCloned.add(new WordPattern(i, l));
					buildSpliTuples(wordPatternsCloned, splitTuples, a, b);
				}
			}
		} else {
			WordPattern last = wordPatterns.get(wordPatterns.size() - 1);
			int i = last.nextStart();
			if (i == n || i == n + 1) {
				if (wordPatterns.size() <= nMaxWords) {
					splitTuples.add(buildSpliTuple(wordPatterns, a, b));
				}
			} else {
				for (int l = 1; l <= n - i; l++) {
					List<WordPattern> wordPatternsCloned = wordPatterns.stream().collect(Collectors.toList());
					wordPatternsCloned.add(new WordPattern(i, l));
					buildSpliTuples(wordPatternsCloned, splitTuples, a, b);
				}
			}
		}
	}

	private void loadWords() {
		words = Stream.concat(Stream.concat(oneLetterWords(), twoLetterWords()), Stream.concat(readFileLines(mainDict), readFileLines(thematicDict)))
				.filter(w -> w.length() <= (wordSizeLimit == -1 ? n : wordSizeLimit)).distinct().sorted().toArray(String[]::new);
		wordsPoints = new int[words.length];
		List<String> list = Arrays.asList(words);
		readFileLines(thematicDict).forEach(w -> {
			int pos = list.indexOf(w);
			if (pos != -1)
				wordsPoints[pos] = w.length();
		});
		// System.out.println("allWords: " + Kit.join(words) + " \n" + Kit.join(wordsPoints));
		oneLetterPositions = oneLetterWords().mapToInt(w -> list.indexOf(w)).toArray();
		// Map<Integer, List<String>> wordsPerLength = Stream.of(words).collect(Collectors.groupingBy(s -> s.length()));
		// wordsPerLength.keySet().stream().forEach(i -> System.out.println(i + " : " + Kit.join(wordsPerLength.get(i))));

		wordsWithPoints = IntStream.range(0, n + 1).mapToObj(l -> IntStream.range(0, words.length).filter(i -> words[i].length() == l).mapToObj(i -> {
			return IntStream.range(0, l + 1).map(j -> j < l ? words[i].charAt(j) - 97 : wordsPoints[i]).toArray();
		}).toArray(int[][]::new)).toArray(int[][][]::new);

		// System.out.println("Words =" + Utilities.join(wordsWithPoints));
	}

	@Override
	public void model() {

		loadWords();
		nMaxWords = nMaxWords == -1 ? (n + 1) / 2 : nMaxWords;

		Var[][] x = array("x", size(n, n), dom(range(N_LETTERS + 1)), "x[i][j] is the (number of) letter at row i and col j; 26 stands for a black point");
		Var[][] br = array("br", size(n, nMaxWords), dom(range(n + 1)),
				"br[i][k] is the benefit of the k+1th word at row i; 0 means that the word is either absent or from the full dictionary");
		Var[][] bc = array("bc", size(n, nMaxWords), dom(range(n + 1)),
				"bc[j][k] is the benfit of the k+1th word at col j; 0 means that the word is either absent or from the full dictionary");

		List<SegmentedTuple> splitTuples = new ArrayList<>();
		forall(range(n), i -> {
			splitTuples.clear();
			buildSpliTuples(new ArrayList<>(), splitTuples, x[i], br[i]);
			((Problem) imp()).addCtr(new CtrExtensionSegmented(((Problem) imp()), (Variable[]) vars(x[i], br[i]), splitTuples.toArray(new SegmentedTuple[0])));
		});
		forall(range(n), j -> {
			splitTuples.clear();
			buildSpliTuples(new ArrayList<>(), splitTuples, columnOf(x, j), bc[j]);
			((Problem) imp())
					.addCtr(new CtrExtensionSegmented(((Problem) imp()), (Variable[]) vars(columnOf(x, j), bc[j]), splitTuples.toArray(new SegmentedTuple[0])));
		});

		// buildSpliTuples(new ArrayList<>(), splitTuples, x[0], br[0]);
		// ((Problem) imp()).addCtr(new CtrExtensionSplit(((Problem) imp()), (Variable[]) vars(x[0], br[0]), splitTuples.toArray(new SplitTuple[0])));
		// splitTuples.clear();
		// buildSpliTuples(new ArrayList<>(), splitTuples, x[1], br[1]);
		// ((Problem) imp()).addCtr(new CtrExtensionSplit(((Problem) imp()), (Variable[]) vars(x[1], br[1]), splitTuples.toArray(new SplitTuple[0])));

		// splitTuples.forEach(st -> System.out.println("ST=" + st));

		// System.out.println("NB splits tuples= " + splitTuples.size() + " nb Subtables =" + splitTuples.stream().mapToInt(s ->
		// s.restrictions.length).sum());

		// atMost(vars(x), takingValue(26), n * 2);
		// atMost(vars(x), takingValue(26), 26); // n * 2);

		maximize(SUM, vars(br, bc));

		// decisionVariables(vars(br, bc));

		// test();
	}

	@Override
	public void prettyDisplay(String[] values) {
		IntStream.range(0, n).forEach(i -> System.out.println(IntStream.range(0, n).mapToObj(j -> {
			int s = Integer.parseInt(values[i * n + j]);
			return s == 26 ? "*" : "" + (char) ('a' + s);
		}).collect(Collectors.joining(""))));
	}

}
