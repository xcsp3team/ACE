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
import org.xcsp.modeler.api.ProblemAPI;

public class SchedulingFS implements ProblemAPI {

	int[][] durations; // durations[i][j] is the duration of operation/machine j for job i

	@Override
	public void model() {
		int n = durations.length, m = durations[0].length;

		int sumDurations = sumOf(valuesFrom(durations, t -> sumOf(t))); // int sumDurations = Stream.of(durations).mapToInt(t -> sumOf(t)).sum();
		int maxTime = sumDurations + 1;

		Var[][] s = array("s", size(n, m), dom(range(maxTime)), "s[i][j] is the start time of the jth operation for the ith job");
		// Var[] e = array("e", size(n), dom(range(maxTime)), "e[i] is the end time of the last operation for the ith job");

		forall(range(n), i -> ordered(s[i], durations[i], INCREASING)).note("operations must be ordered on each job");
		// forall(range(n), i -> equal(e[i], add(s[i][m - 1], durations[i][m - 1]))).note("computing the end time of each job");
		forall(range(m), j -> noOverlap(columnOf(s, j), columnOf(durations, j))).note("no overlap on resources");

		minimize(MAXIMUM, treesFrom(range(n), i -> add(s[i][m - 1], durations[i][m - 1]))).note("minimizing the makespan");
	}
}
