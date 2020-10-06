/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

// Hash Code Pizza (Practice Problem in 2018)
public class HCPizza implements ProblemAPI {

	int minIngredients; // minimum number of each ingredient per slice
	int maxSize; // maximum size (number of cells) per slice
	int[][] pizza; // pizza[i][j] is 1 if tomato, 0 if mushroom

	@NotData
	int nRows, nCols, nPatterns;

	@NotData
	int[][] patterns;

	@NotData
	boolean[][][] possibleSlices;

	@NotData
	List<int[]>[][] overlaps;

	private void buildPatterns() {
		nRows = pizza.length;
		nCols = pizza[0].length;
		patterns = IntStream.range(1, Math.min(maxSize, nRows) + 1).mapToObj(i -> IntStream.range(1, Math.min(maxSize, nCols) + 1)
				.filter(j -> 2 * minIngredients <= i * j && i * j <= maxSize).mapToObj(j -> new int[] { i, j })).flatMap(t -> t).toArray(int[][]::new);
		System.out.println("patterns: " + Utilities.join(patterns));
		nPatterns = patterns.length;
	}

	private boolean possibleSlice(int i, int j, int height, int width) {
		int nMushrooms = 0, nTomatoes = 0;
		for (int ib = i; ib < Math.min(i + height, nRows); ib++)
			for (int jb = j; jb < Math.min(j + width, nCols); jb++)
				if (pizza[ib][jb] == 0)
					nMushrooms++;
				else
					nTomatoes++;
		return nMushrooms >= minIngredients && nTomatoes >= minIngredients;
	}

	private void buildPossibleSlices() {
		overlaps = new List[nRows][nCols];
		possibleSlices = new boolean[nRows][nCols][nPatterns];
		for (int i = 0; i < nRows; i++)
			for (int j = 0; j < nCols; j++)
				for (int k = 0; k < nPatterns; k++) {
					int height = patterns[k][0], width = patterns[k][1];
					possibleSlices[i][j][k] = possibleSlice(i, j, height, width);
					if (possibleSlices[i][j][k]) {
						for (int ib = i; ib < Math.min(i + height, nRows); ib++)
							for (int jb = j; jb < Math.min(j + width, nCols); jb++) {
								if (overlaps[ib][jb] == null)
									overlaps[ib][jb] = new ArrayList<>();
								overlaps[ib][jb].add(new int[] { i, j, k });
							}
					}
				}
		// System.out.println("possibleSlices: " + Utilities.join(possibleSlices));
		// for (int i = 0; i < nRows; i++)
		// for (int j = 0; j < nCols; j++)
		// if (overlaps[i][j] != null)
		// System.out.println(
		// "overlap of (" + i + "," + j + ") :" + overlaps[i][j].stream().map(t -> Utilities.join(t, ",")).collect(Collectors.joining(" ")));
	}

	private int realPatternSize(int i, int j, int k) {
		return (Math.min(i + patterns[k][0], nRows) - i) * (Math.min(j + patterns[k][1], nCols) - j);

	}

	@Override
	public void model() {
		// System.out.println("pizza" + Utilities.join(pizza));
		buildPatterns();
		buildPossibleSlices();

		Var[][][] x = array("x", size(nRows, nCols, nPatterns), (i, j, k) -> dom(0, 1).when(possibleSlices[i][j][k]),
				"x[i][j][k] is 1 iff the slice with left top cell at (i,j) and pattern k is selected");
		Var[][][] s = array("s", size(nRows, nCols, nPatterns), (i, j, k) -> dom(0, realPatternSize(i, j, k)).when(possibleSlices[i][j][k]),
				"s[i][j][k] is the size of the slice with left top cell at (i,j) and pattern k (0 if the slice is not selected)");

		forall(range(nRows).range(nCols).range(nPatterns), (i, j, k) -> {
			if (possibleSlices[i][j][k])
				extension(vars(x[i][j][k], s[i][j][k]), table().add(0, 0).add(1, realPatternSize(i, j, k)));
		});
		System.out.println("pizza1");
		forall(range(nRows).range(nCols), (i, j) -> {
			System.out.println(i + " " + j);
			if (overlaps[i][j] != null && overlaps[i][j].size() > 1) {
				Var[] scope = variablesFrom(overlaps[i][j], t -> x[t[0]][t[1]][t[2]]);
				// if (modelVariant("cnt"))
				// atMost1(scope, takingValue(1));
				// if (modelVariant("sum"))
				sum(scope, LE, 1);

			}
		});
		System.out.println("pizza2");
		maximize(SUM, s);
	}
}
