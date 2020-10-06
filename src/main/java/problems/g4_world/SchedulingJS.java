/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

public class SchedulingJS implements ProblemAPI {

	Job[] jobs;

	class Job {
		int[] durations;
		int[] resources;
		int releaseDate; // 0 if not defined
		int dueDate; // -1 if not defined
	}

	@Override
	public void model() {
		int n = jobs.length, m = jobs[0].durations.length;
		int sumDurations = sumOf(valuesFrom(jobs, j -> sumOf(j.durations)));
		int maxTime = Stream.of(jobs).allMatch(j -> j.dueDate != -1) ? maxOf(valuesFrom(jobs, j -> j.dueDate)) : sumDurations;

		Var[][] s = array("s", size(n, m), dom(range(maxTime)), "s[i][j] is the start time of the jth operation for the ith job");
		// Var[] e = array("e", size(n), dom(range(maxTime)), "e[i] is the end time of the last operation for the ith job");

		forall(range(n), i -> ordered(s[i], jobs[i].durations, INCREASING)).note("operations must be ordered on each job");
		// forall(range(n), i -> equal(e[i], add(s[i][m - 1], jobs[i].durations[m - 1]))).note("computing the end time of each job");
		forall(range(n), i -> {
			if (jobs[i].releaseDate > 0)
				greaterEqual(s[i][0], jobs[i].releaseDate);
			if (jobs[i].dueDate != -1 && jobs[i].dueDate < maxTime - 1)
				lessEqual(s[i][m - 1], (jobs[i].dueDate - jobs[i].durations[m - 1]));
		}).note("respecting release and due dates");
		forall(range(m), j -> {
			Var[] origins = variablesFrom(range(n), i -> s[i][Utilities.indexOf(j, jobs[i].resources)]);
			int[] lengths = valuesFrom(jobs, job -> job.durations[Utilities.indexOf(j, job.resources)]);
			noOverlap(origins, lengths);
		}).note("no overlap on resources");

		minimize(MAXIMUM, treesFrom(range(n), i -> add(s[i][m - 1], jobs[i].durations[m - 1]))).note("minimizing the makespan");
	}
}
