/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.Random;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.GraphMaxAcyclic;
import utility.Kit;

// See Format metis at http://www.cc.gatech.edu/dimacs10/downloads.shtml"
public class GraphMaxAcyclic_Parser extends GraphMaxAcyclic implements ReaderTxt {

	void data() {
		boolean randomGeneration = false; // hard coding
		if (randomGeneration) {
			long seed = 0;
			int n = 20;
			int maxWeight = 30;
			double p = 0.8;
			Random random = new Random(seed);
			Object arcs = range(n).range(n).map((i, j) -> random.nextDouble() > p ? random.nextInt(maxWeight) : 0);
			setDataValues(n, arcs);
		} else {
			String line = nextLine().trim();
			while (line.charAt(0) == '%')
				line = nextLine().trim();
			int[] fl = Utilities.splitToInts(line);
			Kit.control(fl.length == 3 && fl[2] == 1);
			int n = fl[0];
			// int e = fl[1];
			int[][] arcs = new int[n][n];
			for (int i = 0; i < n; i++) {
				int[] t = Utilities.splitToInts(nextLine());
				for (int j = 0; j < t.length; j += 2) {
					arcs[i][t[j] - 1] = t[j + 1];
					// arcs[t[j] - 1][i] = t[j + 1];
				}
			}
			System.out.println("Arcs= " + Utilities.join(arcs));
			setDataValues(n, (Object) arcs);
		}
	}
}
