/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

import utility.Kit;

public class KnightTour implements ProblemAPI {
	int n;

	private int[][] possibleJumps() {
		int[][] jumps = new int[n * n][];
		int[] tmp = new int[8];
		for (int i = 0; i < n; i++)
			for (int j = 0; j < n; j++) {
				int cnt = 0;
				if (i - 2 >= 0) {
					if (j - 1 >= 0)
						tmp[cnt++] = (i - 2) * n + j - 1;
					if (j + 1 < n)
						tmp[cnt++] = (i - 2) * n + j + 1;
				}
				if (i + 2 < n) {
					if (j - 1 >= 0)
						tmp[cnt++] = (i + 2) * n + j - 1;
					if (j + 1 < n)
						tmp[cnt++] = (i + 2) * n + j + 1;
				}
				if (j - 2 >= 0) {
					if (i - 1 >= 0)
						tmp[cnt++] = (i - 1) * n + j - 2;
					if (i + 1 < n)
						tmp[cnt++] = (i + 1) * n + j - 2;
				}
				if (j + 2 < n) {
					if (i - 1 >= 0)
						tmp[cnt++] = (i - 1) * n + j + 2;
					if (i + 1 < n)
						tmp[cnt++] = (i + 1) * n + j + 2;
				}
				jumps[i * n + j] = Kit.sort(Arrays.copyOf(tmp, cnt));
			}
		return jumps;
	}

	private void f(int i, int[] tmp, int[][] jumps, List<int[]> list) {
		if (i == tmp.length)
			list.add(tmp.clone());
		else
			for (int v : jumps[tmp[i - 1]])
				if (IntStream.range(0, i - 1).noneMatch(j -> tmp[j] == v)) {
					tmp[i] = v;
					f(i + 1, tmp, jumps, list);
				}
	}

	private Table buildTable(int length) {
		List<int[]> list = new ArrayList<int[]>();
		int[] tmp = new int[length];
		int[][] jumps = possibleJumps();
		for (int i = 0; i < jumps.length; i++) {
			tmp[0] = i;
			f(1, tmp, jumps, list);
		}
		return table().add(list);
	}

	@Override
	public void model() {
		Var[] x = array("x", size(n * n), dom(range(n * n)), "x[i] is the cell number where the ith knight is put");

		allDifferent(x);

		if (modelVariant(""))
			slide(x, range(n * n), i -> intension(knightAttack(x[i], x[(i + 1) % (n * n)], n)));

		if (modelVariant().startsWith("table")) {
			int r = Integer.parseInt(modelVariant().substring(6)); // we must post table constraints of arity r
			control(r > 1 && n % (r - 1) == 0);
			Table table = buildTable(r);
			slide(x, range(0, n * n, r - 1), i -> extension(variablesFrom(range(r), j -> x[(i + j) % (n * n)]), table));
		}

		instantiation(vars(x[0], x[1]), takingValues(0, n + 2)).tag(SYMMETRY_BREAKING)
				.note("breaking symmetries by putting the first knight in the first cell, and the second knight in the first possible cell");
	}

	@Override
	public void prettyDisplay(String[] values) {
		int[] t = Stream.of(values).mapToInt(s -> Integer.parseInt(s)).toArray();
		DecimalFormat df = new DecimalFormat("00" + "");
		for (int v = 0; v < n * n; v++) {
			if (v % n == 0)
				System.out.println();
			for (int i = 0; i < n * n; i++)
				if (t[i] == v) {
					System.out.print(df.format(i) + " ");
					break;
				}
		}
		System.out.println();
	}
}