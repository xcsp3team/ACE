/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

public class WaterBucket implements ProblemAPI {

	int c1, c2, c3; // capacities of the buckets (in decreasing order)
	int t1, t2, t3; // target
	int h; // horizon

	private Table tableOfCapacities() {
		Table table = table();
		table.add(0, 0, 0); // special case when the goal has been reached
		for (int i = 0; i <= c1; i++)
			for (int j = 0; j <= c2; j++)
				for (int k = 0; k <= c3; k++)
					if (i + j + k == c1)
						table.add(i, j, k);
		return table;
	}

	private boolean connex(int[] tuple1, int[] tuple2) {
		int a1 = tuple1[0], a2 = tuple1[1], a3 = tuple1[2];
		int b1 = tuple2[0], b2 = tuple2[1], b3 = tuple2[2];
		if (a1 == t1 && a2 == t2 && a3 == t3) // after reaching the goal, only 0
			return b1 == 0 && b2 == 0 && b3 == 0;
		if (a1 == 0 && a2 == 0 && a3 == 0) // after reaching the goal, only 0
			return b1 == 0 && b2 == 0 && b3 == 0;
		if (b1 == 0 && b2 == 0 && b3 == 0)
			return false;
		if (IntStream.range(0, 3).allMatch(i -> tuple1[i] != tuple2[i])) // all values different
			return false;
		if (a1 != b1 && a2 != b2) // bucket 1 and bucket 2
			return b1 == 0 || b2 == c2 || b2 == 0 || b1 == c1;
		if (a1 != b1 && a3 != b3) // bucket 1 and bucket 3
			return b1 == 0 || b3 == c3 || b3 == 0 || b1 == c1;
		if (a2 != b2 && a3 != b3) // bucket 2 and bucket 3
			return b2 == 0 || b3 == c3 || b3 == 0 || b2 == c2;
		return false;
	}

	private Table dualTable() {
		Table table = table();
		int[][] tuples = tableOfCapacities().toArray();
		for (int i = 0; i < tuples.length; i++)
			for (int j = 0; j < tuples.length; j++)
				if (connex(tuples[i], tuples[j]))
					table.add(tuples[i][0], tuples[i][1], tuples[i][2], tuples[j][0], tuples[j][1], tuples[j][2]);
		return table;
	}

	private Table goalTable() {
		Table table = table();
		for (int i = 0; i < h; i++) {
			int[] t = new int[h * 3 + 1];
			t[0] = i;
			for (int j = 1; j <= i * 3; j++)
				t[j] = STAR;
			t[i * 3 + 1] = t1;
			t[i * 3 + 2] = t2;
			t[i * 3 + 3] = t3;
			table.add(t);
		}
		return table;
	}

	@Override
	public void model() {
		control(c1 >= c2 && c2 >= c3 && c3 > 0, "Bucket capacities must be in decreasing order");

		Var[][] x = array("x", size(h, 3), (i, j) -> dom(rangeClosed(0, j == 0 ? c1 : j == 1 ? c2 : c3)),
				"x[i][j] is the volume of water in bucket j at time (round) i");
		Var k = var("k", dom(range(h)), "k is the number of transfers of water in order to reach the goal");

		instantiation(x[0], c1, 0, 0).note("Initially, only water in bucket 1");

		Table table = tableOfCapacities();
		forall(range(h), i -> extension(x[i], table));

		Table dualTable = dualTable();
		forall(range(h - 1), i -> extension(vars(x[i], x[i + 1]), dualTable));

		extension(vars(k, x), goalTable());

		minimize(k);

		// System.out.println("Table =" + table);
		// Table table2 = dualTable();
		// System.out.println("Dual =" + table2);
		// System.out.println("Goal =" + goalTable());

	}
}
