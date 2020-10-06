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

import org.xcsp.common.Constants;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.enumerations.EnumerationCartesian;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

import constraints.hard.extension.CtrExtensionSegmented;
import constraints.hard.extension.structures.SegmentedTuple;
import constraints.hard.extension.structures.SegmentedTuple.RestrictionTable;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public class CrosswordDesignSeg2 implements ProblemAPI {

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

	public static class WordPattern {
		public int start, length;

		public WordPattern(int start, int length) {
			this.start = start;
			this.length = length;
		}

		public int nextStart() {
			return start + length + 1;
		}
	}

	class SegmentData {
		WordPattern[] wps;
		int[] prefix;
		int[][][] subtables;

		SegmentData(WordPattern[] wps, int score, int[][][] subtables) {
			this.wps = wps;
			this.prefix = IntStream.range(0, n + 1).map(i -> i == n ? score : Constants.STAR).toArray();
			for (WordPattern wp : wps) {
				int i = wp.start - 1;
				if (i >= 0)
					prefix[i] = N_LETTERS;
				i = wp.start + wp.length;
				if (i < n)
					prefix[i] = N_LETTERS;
			}
			this.subtables = subtables;
		}
	}

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

	private void buildSegmentDatas(Stack<WordPattern> stack, List<SegmentData> list) {
		if (stack.size() == 0) {
			for (int i = 0; i <= 1; i++) { // first word starts at 0 or 1
				for (int l = 1; l <= n - i; l++) {
					stack.push(new WordPattern(i, l));
					buildSegmentDatas(stack, list);
					stack.pop();
				}
			}
		} else {
			WordPattern last = stack.peek();
			int i = last.nextStart();
			if (i == n || i == n + 1) {
				if (stack.size() <= nMaxWords) {
					WordPattern[] t = stack.toArray(new WordPattern[0]);
					int[][] dictSelections = new EnumerationCartesian(Stream.of(t).mapToInt(wp -> thematicWords[wp.length].length > 0 ? 2 : 1).toArray())
							.toArray();
					for (int[] dictSelection : dictSelections) {
						int score = IntStream.range(0, dictSelection.length).map(j -> dictSelection[j] == 0 ? 0 : t[j].length).sum();
						int[][][] subtables = IntStream.range(0, dictSelection.length)
								.mapToObj(j -> dictSelection[j] == 0 ? mainWords[t[j].length] : thematicWords[t[j].length]).toArray(int[][][]::new);
						list.add(new SegmentData(t, score, subtables));
					}
				}
			} else {
				for (int l = 1; l <= n - i; l++) {
					stack.push(new WordPattern(i, l));
					buildSegmentDatas(stack, list);
					stack.pop();
				}
			}
		}
	}

	SegmentData[] buildSegmentDatas() {
		List<SegmentData> list = new ArrayList<>();
		buildSegmentDatas(new Stack<>(), list);
		return list.stream().toArray(SegmentData[]::new);
	}

	SegmentedTuple[] buildSegmentedTuples(SegmentData[] segmentDatas, Var[] vars) {
		SegmentedTuple[] m = new SegmentedTuple[segmentDatas.length];
		for (int j = 0; j < m.length; j++) {
			WordPattern[] wordPatterns = segmentDatas[j].wps;
			RestrictionTable[] restrictions = new RestrictionTable[wordPatterns.length];
			for (int k = 0; k < restrictions.length; k++) {
				WordPattern wp = wordPatterns[k];
				Variable[] subscp = IntStream.range(0, wp.length).mapToObj(i -> vars[wp.start + i]).toArray(Variable[]::new);
				restrictions[k] = new RestrictionTable(subscp, segmentDatas[j].subtables[k]);
			}
			m[j] = new SegmentedTuple(segmentDatas[j].prefix, restrictions);
		}
		return m;
	}

	@Override
	public void model() {
		loadWords();
		nMaxWords = nMaxWords == -1 ? (n + 1) / 2 : nMaxWords;

		int[] allScores = vals(0, range(3, n + 1)); // 1 and 2 are not possible because no thematic word of that size

		Var[][] x = array("x", size(n, n), dom(range(N_LETTERS + 1)), "x[i][j] is the (number of) letter at row i and col j; 26 stands for a black point");
		Var[] br = array("br", size(n), dom(allScores), "br[i] is the benefit at row i; 0 means that all words are from the full dictionary");
		Var[] bc = array("bc", size(n), dom(allScores), "bc[j] is the benefit at col j; 0 means that all words are from the full dictionary");

		SegmentData[] segmentDatas = buildSegmentDatas();
		forall(range(n), i -> ((Problem) imp())
				.addCtr(new CtrExtensionSegmented(((Problem) imp()), (Variable[]) vars(x[i], br[i]), buildSegmentedTuples(segmentDatas, x[i]))));
		forall(range(n), j -> ((Problem) imp()).addCtr(
				new CtrExtensionSegmented(((Problem) imp()), (Variable[]) vars(columnOf(x, j), bc[j]), buildSegmentedTuples(segmentDatas, columnOf(x, j)))));

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
