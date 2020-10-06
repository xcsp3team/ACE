/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.ArrayList;
import java.util.List;

import problems.ReaderFile.ReaderDzn;
import problems.g4_world.Wwtpp;
import utility.Kit;

//java abscon.Resolution problems.generators.WwtppReader ~/instances/minizinc-benchmarks-master/wwtpp-real/ex05680_2400_100.dzn -model=smt -ev => sat in 100s
public class WwtppReaderZ extends Wwtpp implements ReaderDzn {

	void data() {
		int nIndustries = nextInt();
		int nPeriods = nextInt();
		int plantCapacity = nextInt();
		int[] tankFlow = nextInt1D();
		int[] tankCapacity = nextInt1D();
		int[][] sd = nextInt2Db();
		List<int[]> list = new ArrayList<>();
		for (int i = 0; i < nIndustries; i++) {
			for (int j = 0; j < nPeriods - 1;) {
				if (sd[i][j] == 0 || sd[i][j + 1] == 0)
					j++;
				else {
					int k = j + 2;
					while (k < nPeriods && sd[i][k] != 0)
						k++;
					list.add(new int[] { i, j, k }); // industry and range (from, to) on periods
					j = k;
				}
			}
		}
		int[][] spans = Kit.intArray2D(list);
		// System.out.println(nIndustries + " " + nPeriods + " " + plantCapacity);
		// System.out.println(Kit.join(tankFlow) + "\n" + Kit.join(tankCapacity));
		// System.out.println("d=" + Kit.join(sd));
		// System.out.println("spans=" + Kit.join(spans));
		setDataValues(nIndustries, nPeriods, plantCapacity, tankFlow, tankCapacity, sd, spans);
	}
}
