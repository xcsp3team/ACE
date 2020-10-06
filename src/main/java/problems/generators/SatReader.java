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
import java.util.TreeSet;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.Sat;
import utility.Kit;

public class SatReader extends Sat implements ReaderTxt {

	void data() {
		scanner().findWithinHorizon("p cnf", 0);
		int n = nextInt(); // #Vars
		int e = nextInt(); // #Ctrs
		TreeSet<Integer> set = new TreeSet<>();
		List<int[]> cls = new ArrayList<>();
		while (imp().fileScanner().hasNext()) {
			List<Integer> list = new ArrayList<>();
			for (int v = nextInt(); v != 0; v = nextInt())
				list.add(v);
			list.stream().forEach(v -> set.add(Math.abs(v)));
			cls.add(Kit.intArray(list));
		}
		int[][] clauses = cls.stream().toArray(int[][]::new);
		Kit.control(n == set.size() && set.first() == 1 && set.last() == set.size() && e == clauses.length, () -> n + " " + set.size() + " " + e);
		setDataValues(n, e, clauses);
	}

}
