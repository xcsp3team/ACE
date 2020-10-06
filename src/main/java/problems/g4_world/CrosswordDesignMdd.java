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
import java.util.List;
import java.util.Stack;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.enumerations.EnumerationCartesian;
import org.xcsp.common.structures.Transitions;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

import constraints.hard.extension.structures.MDDCD;
import problem.Problem;
import problems.g4_world.CrosswordDesignSeg2.WordPattern;
import utility.Kit;

public class CrosswordDesignMdd implements ProblemAPI {

	private static final int BLACK_CELL = 0;

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

	int[] buildPattern(Stack<WordPattern> wordPatterns) {
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

	void buildPatterns(Stack<WordPattern> stack, List<int[]> list) {
		if (stack.size() == 0) {
			for (int i = 0; i <= 1; i++) {
				for (int l = 1; l <= n - i; l++) {
					stack.push(new WordPattern(i, l));
					buildPatterns(stack, list);
					stack.pop();
				}
			}
		} else {
			WordPattern last = stack.peek();
			int i = last.nextStart();
			if (i == n || i == n + 1) {
				if (stack.size() <= nMaxWords)
					list.add(buildPattern(stack));
			} else {
				for (int l = 1; l <= n - i; l++) {
					stack.push(new WordPattern(i, l));
					buildPatterns(stack, list);
					stack.pop();
				}
			}
		}
	}

	List<int[]> buildPatterns() {
		List<int[]> list = new ArrayList<>();
		buildPatterns(new Stack<>(), list);
		// list.stream().forEach(s -> System.out.println(Kit.join(s)));
		return list;
	}

	@NotData
	int nMerges;

	@NotData
	boolean tetestOnlyOneMdd = true;

	private MDDCD mddFrom(MDDCD mddBlackCell, MDDCD[] mddMainDicts, MDDCD[] mddThemDicts, int... pattern) {
		MDDCD mdd = null;
		int[][] dictSelections = new EnumerationCartesian(IntStream.of(pattern).map(v -> v == BLACK_CELL ? 1 : thematicWords[v].length > 0 ? 2 : 1).toArray())
				.toArray(); // 2 because two dictionaries : 0 stands for the main dictionary and 1 stands for the thematic dictionary
		for (int[] dictSelection : dictSelections) {
			int score = IntStream.range(0, pattern.length).map(i -> dictSelection[i] == 0 ? 0 : pattern[i]).sum();

			MDDCD[] mddSequence = new MDDCD[pattern.length + 1];
			for (int i = 0; i < pattern.length; i++)
				mddSequence[i] = new MDDCD(
						pattern[i] == BLACK_CELL ? mddBlackCell : dictSelection[i] == 0 ? mddMainDicts[pattern[i]] : mddThemDicts[pattern[i]]);
			mddSequence[pattern.length] = new MDDCD(score);
			MDDCD g = MDDCD.concat(mddSequence);
			nMerges++;
			mdd = mdd == null ? g : new MDDCD(mdd, g);
			// mdd.root.display(0, new HashMap<Integer, MDDNodeFake>());
		}
		return mdd;
	}

	private List<MDDCD> buildMDD() {
		MDDCD mddBlackCell = new MDDCD(N_LETTERS);
		MDDCD[] mddMainDicts = IntStream.range(0, n + 1).mapToObj(i -> new MDDCD(mainWords[i])).toArray(MDDCD[]::new);
		for (MDDCD m : mddMainDicts)
			System.out.println("NNodes = " + m.nNodes());
		MDDCD[] mddThemDicts = IntStream.range(0, n + 1).mapToObj(i -> new MDDCD(thematicWords[i])).toArray(MDDCD[]::new);

		List<int[]> patterns = buildPatterns();
		List<MDDCD> gs = new ArrayList<>();

		int cnt = 0;

		if (modelVariant("or")) {
			// List<MDDCD> gs = new ArrayList<>();
			for (int i = patterns.size() - 1; i >= 0; i--) {
				System.out.println("passage " + i + " " + Kit.getFormattedUsedMemorySize() + " for pattern " + Kit.join(patterns.get(i)));
				int[] pattern = patterns.get(i);
				int[][] dictSelections = new EnumerationCartesian(
						IntStream.of(pattern).map(v -> v == BLACK_CELL ? 1 : thematicWords[v].length > 0 ? 2 : 1).toArray()).toArray();
				for (int[] dictSelection : dictSelections) {
					int score = IntStream.range(0, pattern.length).map(j -> dictSelection[j] == 0 ? 0 : pattern[j]).sum();

					MDDCD[] mddSequence = new MDDCD[pattern.length + 1];
					for (int j = 0; j < pattern.length; j++) {
						mddSequence[j] = MDDCD
								.copy(pattern[j] == BLACK_CELL ? mddBlackCell : dictSelection[j] == 0 ? mddMainDicts[pattern[j]] : mddThemDicts[pattern[j]]);
						System.out.println("nNodes " + mddSequence[j].nNodes());
					}

					// mddSequence[j] = new MDDCD(
					// pattern[j] == BLACK_CELL ? mddBlackCell : dictSelection[j] == 0 ? mddMainDicts[pattern[j]] : mddThemDicts[pattern[j]]);

					mddSequence[pattern.length] = new MDDCD(score);
					MDDCD g = MDDCD.concat(mddSequence);
					// System.out.println("Before");
					// g.root.display(0, new HashMap<>());

					// System.out.println("Adding size=" + cnt);
					g.recursiveRenaming();
					// System.out.println("After");
					// g.root.display(0, new HashMap<>());

					gs.add(g);

					cnt += g.nNodes();
					// mdd = mdd == null ? g : new MDDCD(mdd, g);
					// mdd.root.display(0, new HashMap<Integer, MDDNodeFake>());
				}
				// gs[i] = mddFrom(mddBlackCell, mddMainDicts, mddThemDicts, patterns.get(i));
			}

			// MDDCD g1 = mddFrom(mddBlackCell, mddMainDicts, mddThemDicts, patterns.get(patterns.size() - 1));
			// System.out.println("g1");
			// g1.root.display(0, new HashMap<>());
			// MDDCD g2 = mddFrom(mddBlackCell, mddMainDicts, mddThemDicts, patterns.get(patterns.size() - 2));
			// System.out.println("g2");
			// g2.root.display(0, new HashMap<>());
			// return null;

		} else {
			MDDCD mdd = null;

			for (int i = patterns.size() - 1; i >= 0; i--) {
				MDDCD g = mddFrom(mddBlackCell, mddMainDicts, mddThemDicts, patterns.get(i));
				mdd = mdd == null ? g : new MDDCD(mdd, g); // or between the two mdds
				// System.out.println("nNodes=" + mdd.nNodes());
				// System.out.println(" i = " + i + "/" + patterns.size());
			}
			gs.add(mdd);
			// System.out.println("nMerges:" + nMerges);
		}
		// System.out.println("MDD " + mdd);
		// mdd.root.display(0, new HashMap<>());
		return gs;
	}

	@Override
	public void model() {
		loadWords();

		nMaxWords = nMaxWords == -1 ? (n + 1) / 2 : nMaxWords;

		int[] allScores = vals(0, range(3, n + 1)); // 1 and 2 are not possible because no thematic word of that size
		// for variant 'or' ne holes are permitted, this is why allScores is not used

		Var[][] x = array("x", size(n, n), dom(range(N_LETTERS + 1)), "x[i][j] is the (number of) letter at row i and col j; 26 stands for a black point");
		Var[] br = array("br", size(n), dom(range(n + 1)), "br[i] is the benefit at row i; 0 means that all words are from the full dictionary");
		Var[] bc = array("bc", size(n), dom(range(n + 1)), "bc[j] is the benefit at col j; 0 means that all words are from the full dictionary");

		// Var[] br = array("br", size(n), dom(allScores), "br[i] is the benefit at row i; 0 means that all words are from the full dictionary");
		// Var[] bc = array("bc", size(n), dom(allScores), "bc[j] is the benefit at col j; 0 means that all words are from the full dictionary");

		List<MDDCD> mdds = buildMDD();

		if (modelVariant("")) {

			Transitions transitions = mdds.get(0).transitions();
			// System.out.println(transitions);

			forall(range(n), i -> mdd(vars(x[i], br[i]), transitions));
			forall(range(n), j -> mdd(vars(columnOf(x, j), bc[j]), transitions));
		}
		if (modelVariant("or")) {
			MDDCD[] t = mdds.stream().toArray(MDDCD[]::new);

			forall(range(n), i -> ((Problem) imp()).mddOr(vars(x[i], br[i]), t));
			forall(range(n), j -> ((Problem) imp()).mddOr(vars(columnOf(x, j), bc[j]), t));

			// sum(vars(br, bc), NE, 0);

		}

		maximize(SUM, vars(br, bc));
	}

	@Override
	public void prettyDisplay(String[] values) {
		IntStream.range(0, n).forEach(i -> System.out.println(IntStream.range(0, n).mapToObj(j -> {
			int s = Integer.parseInt(values[i * n + j]);
			return s == 26 ? "*" : "" + (char) ('a' + s);
		}).collect(Collectors.joining(""))));
	}

}
