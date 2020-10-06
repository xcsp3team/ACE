/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Scanner;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

// first model without short table constraints of large scope
public class CrosswordDesignFirstUnfinished implements ProblemAPI {

	private static final String[] letters = { "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z" };

	int nRows, nCols, nMaxRowWords, nMaxColWords;
	String[] basicWords;
	String[] themeWords;

	@NotData
	String[] allWords; // two dictionaries merged

	@NotData
	boolean[] fromThemeWords;

	@NotData
	int[] oneLetterPositions;

	private void buildUniqueDictionary() {
		allWords = Stream.concat(Stream.of(letters), Stream.concat(Stream.of(basicWords), Stream.of(themeWords))).filter(w -> w.length() <= nRows).distinct()
				.sorted().toArray(String[]::new);
		fromThemeWords = new boolean[allWords.length];
		List<String> list = Arrays.asList(allWords);
		Stream.of(themeWords).forEach(w -> fromThemeWords[list.indexOf(w)] = true);
		// System.out.println("allWords: " + Kit.join(allWords) + " \n" + Kit.join(fromThemeWords));
		oneLetterPositions = Stream.of(letters).mapToInt(l -> list.indexOf(l)).toArray();
	}

	private int[][] buildTableForTwoSuccessiveWords() {
		List<int[]> list = new ArrayList<>();
		list.add(tuple(-1, 0, -1));
		for (int p = 0; p < nRows; p++)
			for (int s = 1; s <= nRows; s++)
				if (p + s <= nRows)
					list.add(p + s <= 11 ? tuple(p, s, p + s + 1) : tuple(p, s, -1));
		return list.stream().toArray(int[][]::new);
	}

	@Override
	public void model() {
		assert nRows == nCols;
		buildUniqueDictionary();

		Var[][] r = array("r", size(nRows, nMaxRowWords), dom(range(-1, allWords.length)), "r[i][k] is the (index of) kth word at row i; -1 means 'no word'");
		Var[][] c = array("c", size(nCols, nMaxColWords), dom(range(-1, allWords.length)), "c[j][k] is the (index of) kth word at col j; -1 means 'no word'");
		Var[][] pr = array("pr", size(nRows, nMaxRowWords), dom(range(-1, nCols)),
				"pr[i][k] is the position (index of column) of the kth word at row i; -1 means 'no position' because 'no word'");
		Var[][] pc = array("pc", size(nCols, nMaxColWords), dom(range(-1, nRows)),
				"pc[j][k] is the position (index of row) of the kth word at col j; -1 means 'no position' because 'no word'");
		Var[][] sr = array("sr", size(nRows, nMaxRowWords), dom(range(nCols + 1)),
				"sr[i][k] is the size of the kth word at row i; 0 means 'no size' because 'no word'");
		Var[][] sc = array("sc", size(nCols, nMaxColWords), dom(range(nRows + 1)),
				"sc[j][k] is the size of the kth word at col j; 0 means 'no size' because 'no word'");
		// Var[][] br = array("br", size(nRows, nMaxRowWords), dom(range(nCols + 1)),
		// "br[i][k] is the benefit of the kth word at row i; 0 means that the word is either absent or from the full dictionary");
		// Var[][] bc = array("bc", size(nCols, nMaxColWords), dom(range(nRows + 1)),
		// "bc[j][k] is the benfit of the kth word at col j; 0 means that the word is either absent or from the full dictionary");

		Var[] jr = array("jr", size(nRows), dom(range((nRows + 1) / 2)), "jr[i] is the number of black cells (jokers) at row i");
		Var[] jc = array("jc", size(nCols), dom(range((nCols + 1) / 2)), "jc[j] is the number of black cells (jokers) at col j");

		Var[][] x = array("x", size(nRows, nCols), dom(range(letters.length + 1)),
				"x[i][j] is the (number of) letter at row i and col j; 26 stands for a black point");

		Var[][] jx = array("jx", size(nRows, nCols), dom(0, 1), "jx[i][j] is true iff the letter at row i and col j is a black cell (joker)");

		int[][] sizesTable = IntStream.range(-1, allWords.length).mapToObj(i -> tuple(i, i == -1 ? 0 : allWords[i].length())).toArray(int[][]::new);
		// System.out.println("sizesTable: " + Kit.join(sizesTable));
		forall(range(nRows).range(nMaxRowWords), (i, k) -> extension(vars(r[i][k], sr[i][k]), sizesTable)).note("linking row words with their sizes");
		forall(range(nCols).range(nMaxColWords), (j, k) -> extension(vars(c[j][k], sc[j][k]), sizesTable)).note("linking col words with their sizes");

		int[][] succsTable = buildTableForTwoSuccessiveWords();
		// System.out.println("succsTable: " + Kit.join(succsTable));
		forall(range(nRows).range(nMaxRowWords - 1), (i, k) -> extension(vars(pr[i][k], sr[i][k], pr[i][k + 1]), succsTable))
				.note("linking row words and positions (according to their sizes)");
		forall(range(nCols).range(nMaxColWords - 1), (j, k) -> extension(vars(pc[j][k], sc[j][k], pc[j][k + 1]), succsTable))
				.note("linking col words and positions (according to their sizes)");

		// ((Problem) imp()).addCtr(new GridLazy((Problem) imp(), (Variable[][]) r, (Variable[][]) pr, (Variable[][]) sr, (Variable[][]) x));

		allDifferent(vars(r, c), exceptValues(IntStream.range(-1, oneLetterPositions.length).map(i -> i == -1 ? -1 : oneLetterPositions[i]).toArray()));

		forall(range(nRows).range(nCols), (i, j) -> equivalence(eq(x[i][j], 26), eq(jx[i][j], 1)));
		forall(range(nRows), i -> sum(jx[i], EQ, jr[i]));
		forall(range(nRows), j -> sum(columnOf(jx, j), EQ, jc[j]));

		forall(range(nRows), i -> sum(vars(sr[i], jr[i]), EQ, nCols));
		forall(range(nCols), j -> sum(vars(sc[j], jc[j]), EQ, nRows));

		exactly(vars(x), 26, 26); // replace with atMost, later ; to be transformed in a constraint sum ???

		forall(range(nRows), i -> implication(eq(r[i][nMaxRowWords - 2], -1), eq(r[i][nMaxRowWords - 1], -1)));
		forall(range(nCols), j -> implication(eq(c[j][nMaxColWords - 2], -1), eq(c[j][nMaxColWords - 1], -1)));

		// replace lazy gri with table constraints of arity 15
		// rik pik x[i] // et ajouter sik ?? et ajouter pik+1
		// 10 0 hello bp * * * **
		// 10 1 bp hello bp * * * *
		// 10 2 * bp hello bp * * *
		// here, 10 stands for hello
		// and add a constraint forcing the first word to be not equal to -1

	}

	public static void main(String[] args) {
		try (Scanner scanner = new Scanner(new File(args[0])); PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(args[0] + ".fmt")))) {
			while (scanner.hasNextLine())
				out.println("\"" + scanner.nextLine() + "\", ");
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
