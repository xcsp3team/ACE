/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.hard.extension.structures.SmartTuple;
import problem.Problem;

public class Wwtpp implements ProblemAPI {
	int nIndustries, nPeriods, plantCapacity;
	int[] tankFlow, tankCapacity;
	int[][] sd; // schedule flow of discharge
	int[][] spans;

	private Table shortTableFor(int i) {
		Table table = table(0, STAR);
		for (int v = tankFlow[i]; v <= tankCapacity[i]; v++)
			table.add(tankFlow[i], v);
		for (int v = 1; v <= Math.min(tankFlow[i], tankCapacity[i]); v++)
			table.add(v, v);
		return table;
	}

	@Override
	public void model() {
		Var[][] b = array("b", size(nIndustries, nPeriods), (i, j) -> (j == 0 && sd[i][0] == 0) || j == nPeriods - 1 ? dom(0) : dom(range(tankCapacity[i] + 1)),
				"b[i][j] is the flow stored in buffer i at the end of period j");
		Var[][] d = array("d", size(nIndustries, nPeriods), (i, j) -> j == 0 ? dom(0) : dom(range(tankFlow[i] + 1)),
				"d[i][j] is the flow discharged from buffer (or industry) i during time period j");
		Var[][] c = array("c", size(nIndustries, nPeriods), (i, j) -> sd[i][j] == 0 ? null : dom(0, sd[i][j]),
				"c[i][j] is the actual capacity requirement of industry i during time period j");

		forall(range(nPeriods), j -> sum(vars(select(c, (i, k) -> k == j && c[i][k] != null), columnOf(d, j)), LE, plantCapacity))
				.note("not exceeding the Wastewater Treatment Plant");

		forall(range(nIndustries), i -> {
			if (sd[i][0] != 0)
				sum(vars(b[i][0], c[i][0]), EQ, sd[i][0]);
		}).note("managing scheduled discharge flows at period 0");

		forall(range(nIndustries).range(1, nPeriods), (i, j) -> {
			if (sd[i][j] != 0)
				sum(vars(b[i][j], b[i][j - 1], d[i][j], c[i][j]), vals(1, -1, 1, 1), EQ, sd[i][j]);
			else
				sum(vars(b[i][j], b[i][j - 1], d[i][j]), vals(1, -1, 1), EQ, 0);
		}).note("managing scheduled discharge flows at all periods except 0");

		forall(range(nIndustries).range(1, nPeriods), (i, j) -> {
			Var[] scp = vars(d[i][j], b[i][j - 1]);
			if (j == nPeriods - 1 || j - 1 == nPeriods - 1 || (j - 1 == 0 && sd[i][0] == 0))
				extension(scp, table("(0,0)"));
			else if (modelVariant(""))
				extension(scp, shortTableFor(i).toOrdinaryTableArray(tankFlow[i] + 1, tankCapacity[i] + 1));
			else if (modelVariant("short"))
				extension(scp, shortTableFor(i));
			else if (modelVariant("smt")) {
				SmartTuple st1 = new SmartTuple(tuple(0, STAR));
				SmartTuple st2 = new SmartTuple(tuple(tankFlow[i], STAR), ge(b[i][j - 1], tankFlow[i]));
				SmartTuple st3 = new SmartTuple(eq(d[i][j], b[i][j - 1]));
				((Problem) imp()).smart(scp, st1, st2, st3);
			}
		}).note("ensuring compatibility between stored and discharge flows");

		forall(range(spans.length), k -> {
			int[] span = spans[k];
			Var[] scp = select(c[span[0]], span[1], span[2]);
			extension(scp, table(repeat(0, scp.length), select(sd[span[0]], span[1], span[2])));
		}).note("spanning constraints");

	}
}
