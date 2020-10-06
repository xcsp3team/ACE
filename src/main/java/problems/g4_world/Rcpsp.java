package problems.g4_world;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class Rcpsp implements ProblemAPI {
	int horizon;
	int[] resourceCapacities;
	Job[] jobs;

	class Job {
		int duration;
		int[] successors;
		int[] requiredQuantities;
	}

	@Override
	public void model() {
		int nJobs = jobs.length;

		Var[] s = array("s", size(nJobs), i -> i == 0 ? dom(0) : dom(range(horizon)), "s[i] is the starting time of the ith job");

		forall(range(nJobs).range(nJobs), (i, j) -> {
			if (j < jobs[i].successors.length)
				lessEqual(add(s[i], jobs[i].duration), s[jobs[i].successors[j]]);
		}).note("precedence constraints");

		forall(range(resourceCapacities.length), j -> {
			int[] indexes = select(range(nJobs), i -> jobs[i].requiredQuantities[j] > 0);
			Var[] origins = variablesFrom(indexes, index -> s[index]);
			int[] lengths = valuesFrom(indexes, index -> jobs[index].duration);
			int[] heights = valuesFrom(indexes, index -> jobs[index].requiredQuantities[j]);
			cumulative(origins, lengths, heights, resourceCapacities[j]);
		}).note("resource constraints");
		minimize(s[nJobs - 1]);
	}
}
// int[] t = range(nJobs).select(i -> jobs[i].requiredQuantities[j] > 0);
// int[] t = IntStream.range(0, nJobs).filter(i -> jobs[i].requiredQuantities[j] > 0).toArray();

// Var[] origins = Arrays.stream(t).mapToObj(i -> s[i]).toArray(Var[]::new);
// int[] lengths = Arrays.stream(t).map(i -> durations[i]).toArray();
// int[] heights = Arrays.stream(t).map(i -> requiredQuantities[i][j]).toArray();
