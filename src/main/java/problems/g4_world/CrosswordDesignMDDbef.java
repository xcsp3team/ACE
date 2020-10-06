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
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.enumerations.EnumerationCartesian;
import org.xcsp.common.structures.Transitions;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

import constraints.hard.extension.structures.MDDCDbef;
import problems.g4_world.CrosswordDesignSeg2.WordPattern;
import utility.Kit;

public class CrosswordDesignMDDbef implements ProblemAPI {

	private static final int BLACK_CELL = 0;

	private static final int MAIN_DICTIONARY = 0;

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
	int[][][] mainWords;

	@NotData
	int[][][] thematicWords;

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

	private void loadWords() {
		String[] mw = Stream.concat(Stream.concat(oneLetterWords(), twoLetterWords()), readFileLines(mainDict))
				.filter(w -> w.length() <= (wordSizeLimit == -1 ? n : wordSizeLimit)).distinct().sorted().toArray(String[]::new);
		String[] tw = readFileLines(thematicDict).filter(w -> w.length() <= (wordSizeLimit == -1 ? n : wordSizeLimit)).distinct().sorted()
				.toArray(String[]::new);
		mainWords = IntStream.range(0, n + 1).mapToObj(l -> IntStream.range(0, mw.length).filter(i -> mw[i].length() == l).mapToObj(i -> {
			return IntStream.range(0, l).map(j -> mw[i].charAt(j) - 97).toArray();
		}).toArray(int[][]::new)).toArray(int[][][]::new);
		Kit.control(IntStream.range(1, n + 1).allMatch(l -> mainWords[l].length > 0));
		thematicWords = IntStream.range(0, n + 1).mapToObj(l -> IntStream.range(0, tw.length).filter(i -> tw[i].length() == l).mapToObj(i -> {
			return IntStream.range(0, l).map(j -> tw[i].charAt(j) - 97).toArray();
		}).toArray(int[][]::new)).toArray(int[][][]::new);
	}

	/**** Begin Part on MDDs */

	int[] buildPatternTuple(List<WordPattern> wordPatterns) {
		List<Integer> list = new ArrayList<>();
		if (wordPatterns.get(0).start > 0)
			list.add(0);
		for (int i = 0; i < wordPatterns.size(); i++) {
			list.add(wordPatterns.get(i).length);
			if (i < wordPatterns.size() - 1)
				list.add(0);
		}
		if (wordPatterns.get(wordPatterns.size() - 1).nextStart() <= n)
			list.add(0);
		return list.stream().mapToInt(i -> i).toArray();
	}

	List<int[]> buildPatternTuples(List<WordPattern> wordPatterns, List<int[]> tuples) {
		if (wordPatterns.size() == 0) {
			for (int i = 0; i <= 1; i++) {
				for (int l = 1; l <= n - i; l++) {
					List<WordPattern> wordPatternsCloned = wordPatterns.stream().collect(Collectors.toList());
					wordPatternsCloned.add(new WordPattern(i, l));
					buildPatternTuples(wordPatternsCloned, tuples);
				}
			}
		} else {
			WordPattern last = wordPatterns.get(wordPatterns.size() - 1);
			int i = last.nextStart();
			if (i == n || i == n + 1) {
				if (wordPatterns.size() <= nMaxWords) {
					tuples.add(buildPatternTuple(wordPatterns));
				}
			} else {
				for (int l = 1; l <= n - i; l++) {
					List<WordPattern> wordPatternsCloned = wordPatterns.stream().collect(Collectors.toList());
					wordPatternsCloned.add(new WordPattern(i, l));
					buildPatternTuples(wordPatternsCloned, tuples);
				}
			}
		}
		return tuples;
	}

	@NotData
	MDDCDbef mddStar, mddMainDicts[], mddThemDicts[];

	@NotData
	Set<Integer> scores = new HashSet<>();

	@NotData
	int nMerges;

	private MDDCDbef mddFrom(int... pattern) {
		MDDCDbef mdd = null;
		int[][] dictSelections = new EnumerationCartesian(IntStream.of(pattern).map(v -> v == BLACK_CELL ? 1 : thematicWords[v].length > 0 ? 2 : 1).toArray())
				.toArray(); // 2 because two dictionaries : 0 stands for the main dictionary and 1 stands for the thematic dictionary
		for (int[] dictSelection : dictSelections) {
			System.out.println("t=" + Kit.join(dictSelection) + " p=" + Kit.join(pattern));
			int score = IntStream.range(0, pattern.length).map(i -> dictSelection[i] == 0 ? 0 : pattern[i]).sum();
			System.out.println("score" + score);
			scores.add(score);
			MDDCDbef[] mddSequence = IntStream.range(0, pattern.length + 1)
					.mapToObj(i -> i == pattern.length ? new MDDCDbef(score)
							: new MDDCDbef(pattern[i] == BLACK_CELL ? mddStar : dictSelection[i] == 0 ? mddMainDicts[pattern[i]] : mddThemDicts[pattern[i]]))
					.toArray(MDDCDbef[]::new);
			MDDCDbef g = MDDCDbef.concat(mddSequence);
			// g.root.display(0, new HashMap<Integer, MDDNodeFake>());
			nMerges++;
			mdd = mdd == null ? g : new MDDCDbef(mdd, g);
			// f.root.display(0, new HashMap<Integer, MDDNodeFake>());
		}
		return mdd;
	}

	private MDDCDbef buildMDD() {
		List<int[]> patterns = buildPatternTuples(new ArrayList<>(), new ArrayList<>());
		patterns.stream().forEach(s -> System.out.println(Kit.join(s)));

		mddStar = new MDDCDbef(N_LETTERS);
		mddMainDicts = IntStream.range(0, n + 1).mapToObj(i -> new MDDCDbef(mainWords[i])).toArray(MDDCDbef[]::new);
		mddThemDicts = IntStream.range(0, n + 1).mapToObj(i -> new MDDCDbef(thematicWords[i])).toArray(MDDCDbef[]::new);

		// MDDFake h = merge(3, 0, 4);
		// MDDFake g = MDDFake.merge(fromPattern(fakes, 7, 0, 2));
		// MDDFake h = new MDDFake(f, g);
		// f.root.display(0, new HashMap<Integer, MDDNodeFake>());

		MDDCDbef f = mddFrom(patterns.get(patterns.size() - 1));
		// f.displayTuples();
		// f.root.display(0, new HashMap<Integer, MDDNodeFake>());
		for (int i = patterns.size() - 2; i >= 0; i--) {
			MDDCDbef g = mddFrom(patterns.get(i));
			// g.root.display(0, new HashMap<Integer, MDDNodeFake>());
			f = new MDDCDbef(f, g); // or between the two mdds
			System.out.println("nNodes=" + f.nNodes()); // root.display(0, new HashMap<Integer, MDDNodeFake>());
			System.out.println(" i = " + i + "/" + patterns.size());
		}
		System.out.println("nMerges:" + nMerges);
		return f;
	}

	/**** End Part on MDDs */

	@Override
	public void model() {
		loadWords();
		Transitions trs = buildMDD().transitions();
		System.out.println(trs);

		nMaxWords = nMaxWords == -1 ? (n + 1) / 2 : nMaxWords;
		int[] scs = scores.stream().mapToInt(i -> i).sorted().toArray();

		Var[][] x = array("x", size(n, n), dom(range(N_LETTERS + 1)), "x[i][j] is the (number of) letter at row i and col j; 26 stands for a black point");
		Var[] br = array("br", size(n), dom(scs), "br[i] is the benefit at row i; 0 means that all words are from the full dictionary");
		Var[] bc = array("bc", size(n), dom(scs), "bc[j] is the benefit at col j; 0 means that all words are from the full dictionary");

		forall(range(n), i -> mdd(vars(x[i], br[i]), trs));
		forall(range(n), j -> mdd(vars(columnOf(x, j), bc[j]), trs));

		maximize(SUM, vars(br, bc));
	}

	@Override
	public void prettyDisplay(String[] values) {
		IntStream.range(0, n).forEach(i -> System.out.println(IntStream.range(0, n).mapToObj(j -> {
			int s = Integer.parseInt(values[i * n + j]);
			return s == -1 ? "*" : "" + (char) ('a' + s);
		}).collect(Collectors.joining(""))));
	}

}
