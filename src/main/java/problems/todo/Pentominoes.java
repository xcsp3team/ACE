/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.todo;

import java.util.stream.IntStream;

import org.xcsp.modeler.api.ProblemAPI;

import problems.ReaderFile.ReaderDzn;
import utility.Kit;

public class Pentominoes implements ProblemAPI, ReaderDzn {
	int Q = 1, S = 2, Fstart = 3, Fend = 4, Dstart = 5;

	int width, height, filled, ntiles, size;
	int[][] tiles;
	int[] dfa;

	void data() {
		width = nextInt();
		height = nextInt();
		filled = nextInt();
		ntiles = nextInt();
		size = nextInt();
		System.out.println(width + " " + height + " " + filled + " " + ntiles + " " + size);
		tiles = nextInt2D();
		System.out.println("tiles = " + Kit.join(tiles));
		dfa = nextInt1D();
		System.out.println("dfa = " + Kit.join(dfa));

		int nbStates = tiles[0][0];
		int nbLetters = tiles[0][1];
		int[] finals = IntStream.rangeClosed(tiles[0][2], tiles[0][3]).toArray();
		int[][] transitions = IntStream.range(0, nbStates - 1)
				.mapToObj(i -> select(dfa, IntStream.range(tiles[0][4] + i * nbLetters, tiles[0][4] + i * nbLetters + nbLetters).toArray()))
				.toArray(int[][]::new);
		System.out.println("\nfinals = " + Kit.join(finals));

		System.out.println("\ntransitions = " + Kit.join(transitions));
	}

	@Override
	public void model() {
		// VarInteger[][] b = array("b", size(w + 2, h + 2), dom(range(-1, n - 1)),
		// "b[i][j] is -1 if inoccupied, and the number of a point otherwise. Note the presence of a border.");
		//
		// block(() -> {
		// instantiation(b[0], repeat(-1, h + 2));
		// instantiation(b[w + 1], repeat(-1, h + 2));
		// instantiation(columnOf(b, 0), repeat(-1, w + 2));
		// instantiation(columnOf(b, h + 1), repeat(-1, w + 2));
		// }).note("Cells at the border are inoccupied (-1)");
		//
		// block(() -> {
		// forall(range(n), i -> equal(b[x1[i]][y1[i]], i));
		// forall(range(n), i -> equal(b[x2[i]][y2[i]], i));
		// }).note("End points are put on the board");
		//
		// block(() -> {
		// forall(range(n), i -> exactly(vars(b[x1[i]][y1[i] + 1], b[x1[i] + 1][y1[i]], b[x1[i]][y1[i] - 1], b[x1[i] - 1][y1[i]]), i, 1));
		// forall(range(n), i -> exactly(vars(b[x2[i]][y2[i] + 1], b[x2[i] + 1][y2[i]], b[x2[i]][y2[i] - 1], b[x2[i] - 1][y2[i]]), i, 1));
		// }).note("End points with exactly one horizontal and one vertical neighbour");
		//
		// // TODO To be tested
		// forall(range(1, w).range(1, h), (i, j) -> {
		// if (IntStream.range(0, n - 1).noneMatch(k -> x1[k] == i && y1[k] == j || x2[k] == i && y2[k] == j))
		// ifThen(notEqual(b[i][j], 0), (CtrAlone) count(vars(b[i][j + 1], b[i + 1][j], b[i][j - 1], b[i - 1][j]), b[i][j], EQ, 2));
		// });

	}
}