/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.todo;

import java.util.Arrays;
import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.common.enumerations.EnumerationOfPermutations;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

public class BlockParty implements ProblemAPI {
	int[][] data;

	// Which symbol positions on a cube are next to each other on the same corner.
	// Made by hand, I do not think there is any hope for finding a simple formula that could be used in precomputation :-)
	// Actually it might be divided by three and have a disjunction in link_cube_and_symbols
	// 24 * 4
	// model minizinc, message Pierre Flener 17 Aout 2018 : see Minizinc-Autotabling-modelsmaster
	@NotData
	int[][] pp = { { 21, 12, 7 }, { 23, 17, 11 }, { 24, 4, 18 }, { 22, 8, 3 }, { 1, 6, 16 }, { 2, 14, 20 }, { 4, 18, 24 }, { 3, 22, 8 }, { 7, 21, 12 }, { 5, 10, 15 }, { 6, 16, 1 }, { 8, 3, 22 }, { 16, 1, 6 }, { 15, 5, 10 }, { 13, 9, 19 }, { 14, 20, 2 }, { 18, 24, 4 }, { 20, 2, 14 }, { 19, 13, 9 }, { 17, 11, 23 }, { 12, 7, 21 }, { 11, 23, 17 }, { 9, 19, 13 }, { 10, 15, 5 } };

	@NotData
	int[][] faces = { { 0, 1, 2, 3 }, { 4, 5, 6, 7 }, { 8, 10, 12, 14 }, { 9, 11, 13, 15 }, { 16, 17, 20, 21 }, { 18, 19, 22, 23 } };

	private Table partyTable() {
		int[][] diffEqual = table().add(0, 0, 0, 0).add(1, 1, 1, 1).add(2, 2, 2, 2).add(3, 3, 3, 3).add(allPermutations(4)).toArray();
		// System.out.println("DAta" + Kit.join(diffEqual));
		Table table = table();
		for (int i = 0; i < 64; i++)
			for (int j = 0; j < 64; j++)
				for (int k = 0; k < 64; k++)
					for (int l = 0; l < 64; l++) {
						int[] shape = IntStream.of(i, j, k, l).map(v -> v % 4).toArray();
						if (Arrays.binarySearch(diffEqual, shape, Utilities.lexComparatorInt) < 0)
							continue;
						int[] color = IntStream.of(i, j, k, l).map(v -> (v % 16) / 4).toArray();
						if (Arrays.binarySearch(diffEqual, color, Utilities.lexComparatorInt) < 0)
							continue;
						int[] fill = IntStream.of(i, j, k, l).map(v -> v / 16).toArray();
						if (Arrays.binarySearch(diffEqual, fill, Utilities.lexComparatorInt) < 0)
							continue;
						table.add(i, j, k, l);
					}
		return table;

	}

	@Override
	public void model() {
		int ud = 0, lr = 8, fb = 16;
		int nCubes = 8;
		int nPos = 24, nSymbols = 4 * 4 * 4;

		Var[] cube_at = array("c", size(nCubes), dom(range(nCubes)));
		Var[] symbol_at = array("s", size(nPos), dom(range(nSymbols)));

		allDifferent(cube_at).note("each cube is put at a different place");

		Table table = partyTable();
		System.out.println("Size= " + table.size() + " => " + table);
		forall(range(6), i -> extension(select(symbol_at, faces[i]), table));

		block(() -> {
			equal(cube_at[0], 0);
			lessThan(cube_at[1], cube_at[2]);
			lessThan(cube_at[1], cube_at[4]);
		}).tag(SYMMETRY_BREAKING);

		int[][] m = new EnumerationOfPermutations(4).toArray();

		// System.out.println("DAta" + Kit.join(selectShapes));
		// f();

		// TODO linking cubes and symbols to be finished

	}
}

// private int[][] select(Function<Integer, Integer> f) {
// return IntStream.range(0, 4).mapToObj(target -> IntStream.range(0, 64).filter(i -> f.apply(i) == target).toArray()).toArray(int[][]::new);
// }
//
// @NotData
// int[][] selectShapes = select(v -> v % 4);
//
// @NotData
// int[][] selectColors = select(v -> (v % 16) / 4);
//
// @NotData
// int[][] selectFill = select(v -> v / 16);
