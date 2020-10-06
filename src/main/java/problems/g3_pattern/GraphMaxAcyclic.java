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
import org.xcsp.modeler.api.ProblemAPI;

import constraints.hard.extension.structures.SmartTuple;
import heuristics.variables.HeuristicVariablesDynamic;
import problem.Problem;
import search.backtrack.SolverBacktrack;
import variables.Variable;

public class GraphMaxAcyclic implements ProblemAPI {
	int nNodes;
	public int[][] arcs;

	public static class Flow extends HeuristicVariablesDynamic {

		private int[] maxInFlows;

		private int maxInFlowOf(int[][] arcs, int j) {
			int max = Integer.MIN_VALUE;
			for (int i1 = 0; i1 < arcs.length; i1++)
				for (int i2 = i1 + 1; i2 < arcs.length; i2++)
					for (int i3 = i2 + 1; i3 < arcs.length; i3++)
						if (i1 != j && i2 != j && i3 != j && arcs[i1][j] + arcs[i2][j] + arcs[i3][j] > max)
							max = arcs[i1][j] + arcs[i2][j] + arcs[i3][j];
			return max;
		}

		public Flow(SolverBacktrack solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
			int[][] arcs = ((GraphMaxAcyclic) solver.pb.api).arcs;
			maxInFlows = IntStream.range(0, arcs.length).map(i -> maxInFlowOf(arcs, i)).toArray();
		}

		@Override
		public double scoreOf(Variable x) {
			return x.num < maxInFlows.length ? maxInFlows[x.num] : -100000;
		}
	}

	@Override
	public void model() {
		Var[] x = array("x", size(nNodes), dom(range(nNodes)), "x[i] is the number associated with the ith node");

		allDifferent(x);

		if (modelVariant("") || modelVariant("cnt")) {
			Var[][] a = array("a", size(nNodes, nNodes), (i, j) -> i != j && arcs[i][j] != 0 ? dom(0, 1) : null,
					"a[i][j] is 1 iff the arc from i to j is selected");

			if (modelVariant(""))
				forall(range(nNodes).range(nNodes), (i, j) -> {
					if (a[i][j] != null)
						equivalence(gt(x[i], x[j]), eq(a[i][j], 1));
				});
			else {
				forall(range(nNodes).range(nNodes), (i, j) -> {
					if (a[i][j] != null)
						implication(le(x[i], x[j]), eq(a[i][j], 0));
				});
				forall(range(nNodes), j -> {
					Var[] t = select(a, (i, k) -> k == j && a[i][j] != null); // && arcs[i][j] != 0);
					if (t != null && t.length > 3)
						atMost(t, 1, 3);
				});
			}
			maximize(SUM, a, weightedBy(arcs), onlyOn((i, j) -> a[i][j] != null));
		}

		if (modelVariant("smt")) {
			Var[][] c = array("c", size(nNodes, nNodes), (i, j) -> i < j && (arcs[i][j] != 0 || arcs[j][i] != 0) ? dom(arcs[i][j], arcs[j][i]) : null,
					"c[i][j] is the cost of the link between i and j (whatever the direction)");
			forall(range(nNodes).range(nNodes), (i, j) -> {
				if (i < j && c[i][j] != null) {
					SmartTuple st1 = new SmartTuple(tuple(STAR, STAR, arcs[i][j]), gt(x[i], x[j]));
					SmartTuple st2 = new SmartTuple(tuple(STAR, STAR, arcs[j][i]), lt(x[i], x[j]));
					((Problem) imp()).smart(vars(x[i], x[j], c[i][j]), st1, st2);
				}
			});
			maximize(SUM, select(c, (i, j) -> i < j && c[i][j] != null));
		}
	}
}
