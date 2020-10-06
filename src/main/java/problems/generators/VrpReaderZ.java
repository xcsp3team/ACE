/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import problems.ReaderFile.ReaderDzn;
import problems.g4_world.Vrp;

// java abscon.Resolution problems.generators.VrpReaderZ P-n16-k8.dzn -f=cop -varh=Memory -os=decreasing => optimum=450 in 400s
public class VrpReaderZ extends Vrp implements ReaderDzn {

	void data() {
		int n = nextInt() + 1; // we add the depot (node 0)
		int capacity = nextInt();
		int[] demand = vals(0, nextInt1D()); // 0 as demand for the depot
		int[][] distances = nextInt2D();
		// System.out.println(n + " " + capacity + "\n" + Kit.join(demand) + "\n" + Kit.join(distances));
		setDataValues(n, capacity, demand, distances);
	}

}
