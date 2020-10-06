/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

// java abscon.Resolution problems.patt.OpenStacks 2 problem_15_15_1.dzn -f=cop -os=decreasing -sing=Last -varh=Impact =>optimum 7 in 98s
public class OpenStacks implements ProblemAPI {
	int[][] orders; // orders[i][j] is the jth product of the ith customer

	private Table shortTableFor(int max) {
		return table(0, 0, 0).add(IntStream.range(1, max).mapToObj(i -> tuple(i, STAR, 1))).add(max, 0, 0).add(max, 1, 1);
	}

	private Table shortTable2For(int t) {
		Table table = table().add(IntStream.range(0, t).mapToObj(i -> tuple(STAR, i, 0)))
				.add(IntStream.range(t + 1, orders[0].length).mapToObj(i -> tuple(i, STAR, 0)));
		for (int i = 0; i <= t; i++)
			for (int j = t; j < orders[0].length; j++)
				table.add(i, j, 1);
		return table;
	}

	@Override
	public void model() {
		int n = orders.length, m = orders[0].length;
		if (modelVariant().startsWith("m1")) {
			int[] nProducts = IntStream.range(0, n).map(i -> IntStream.of(orders[i]).sum()).toArray();

			Var[] p = array("p", size(m), dom(range(m)), "p[j] is the period (time) of the jth product");
			Var[][] np = array("np", size(n, m), (i, j) -> dom(range(nProducts[i] + 1)),
					"np[i][j] is the number of products made at time j and required by customer i");
			Var[][] r = array("r", size(n, m), dom(0, 1), "r[i][t] is 1 iff the product made at time t concerns customer i");
			Var[][] o = array("o", size(n, m), dom(0, 1), "o[i][t] is 1 iff the stack is open for customer i at time t");
			Var[] ns = array("ns", size(m), dom(range(m + 1)), "ns[t] is the number of open stacks at time t");

			allDifferent(p);
			forall(range(n).range(m), (i, j) -> element(orders[i], p[j], r[i][j]));
			forall(range(n).range(m), (i, j) -> equal(np[i][j], j == 0 ? r[i][j] : add(np[i][j - 1], r[i][j])));
			forall(range(n).range(m), (i, j) -> {
				Table shortTable = shortTableFor(nProducts[i]);
				int[][] tuples = modelVariant("m1") ? shortTable.toArray() : shortTable.toOrdinaryTableArray(nProducts[i] + 1, 2, 2);
				extension(vars(np[i][j], r[i][j], o[i][j]), tuples);
			});
			forall(range(m), j -> sum(columnOf(o, j), EQ, ns[j]));

			minimize(MAXIMUM, ns);
		}
		if (modelVariant().startsWith("m2")) {
			Var[] p = array("p", size(m), dom(range(m)), "p[j] is the period (time) of the jth product");
			Var[] s = array("s", size(n), dom(range(m)), "s[i] is the starting time of the ith stack");
			Var[] e = array("e", size(n), dom(range(m)), "e[i] is the ending time of the ith stack");
			Var[][] o = array("o", size(n, m), dom(0, 1), "o[i][t] is 1 iff the ith stack is open at time t");
			Var[] ns = array("ns", size(m), dom(range(m + 1)), "ns[t] is the number of open stacks at time t");

			allDifferent(p).note("all products are scheduled at different times");
			forall(range(n), i -> minimum(select(p, j -> orders[i][j] == 1), s[i])).note("computing starting times of stacks");
			forall(range(n), i -> maximum(select(p, j -> orders[i][j] == 1), e[i])).note("computing ending times of stacks");

			forall(range(n).range(m), (i, t) -> {
				Table table = shortTable2For(t);
				extension(vars(s[i], e[i], o[i][t]), modelVariant("m2") ? table.toArray() : table.toOrdinaryTableArray(m, m, 2));
			}).note("inferring when stacks are open");
			forall(range(m), t -> sum(columnOf(o, t), EQ, ns[t])).note("computing the number of open stacks at any time");
			minimize(MAXIMUM, ns).note("minimizing the number of stacks that are simultaneously open");

			// annotateVarhStatic(p);
		}
	}
}
