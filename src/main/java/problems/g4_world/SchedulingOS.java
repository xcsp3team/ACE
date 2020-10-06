/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class SchedulingOS implements ProblemAPI {

	int[][] durations;

	@Override
	public void model() {
		int n = durations.length, m = durations[0].length;
		int sumDurations = sumOf(valuesFrom(durations, t -> sumOf(t)));
		int maxTime = sumDurations + 1; // for GP and Taillard, info about ub is available in original data files (e.g., 1400 for GP)

		Var[][] s = array("s", size(n, m), dom(range(maxTime)), "s[i][j] is the start time of the jth operation for the ith job");
		// Var[] e = array("e", size(n), dom(range(maxTime)), "e[i] is the end time of the last operation for the ith job");
		Var[][] d = array("d", size(n, m), (i, j) -> dom(durations[i]), "d[i][j] is the duration of the jth operation of the ith job");
		Var[][] mc = array("mc", size(n, m), dom(range(m)), "mc[i][j] is the machine used for the jth operation of the ith job");
		Var[][] sd = array("sd", size(n, m), dom(range(maxTime)), "sd[i][k] is the start (dual) time of the kth machine when used for the ith job");

		forall(range(n), i -> ordered(s[i], d[i], INCREASING)).note("operations must be ordered on each job");
		// forall(range(n), i -> equal(e[i], add(s[i][m - 1], d[i][m - 1]))).note("computing the end time of each job");
		forall(range(n), i -> allDifferent(mc[i])).note("each machine must be used for each job");
		forall(range(n).range(m), (i, j) -> extension(vars(mc[i][j], d[i][j]), indexing(durations[i])));
		forall(range(n).range(m), (i, j) -> element(sd[i], mc[i][j], s[i][j])).tag(CHANNELING);
		forall(range(m), j -> noOverlap(columnOf(sd, j), columnOf(durations, j))).note("no overlap on resources");
		forall(range(n), i -> greaterEqual(add(s[i][m - 1], d[i][m - 1]), IntStream.of(durations[i]).sum())).tag(REDUNDANT_CONSTRAINTS);

		minimize(MAXIMUM, treesFrom(range(n), i -> add(s[i][m - 1], d[i][m - 1]))).note("minimizing the makespan");
	}
}
