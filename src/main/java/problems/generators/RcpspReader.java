package problems.generators;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.Rcpsp;
import utility.Kit;

public class RcpspReader extends Rcpsp implements ReaderTxt {

	void data() {
		IntStream.range(0, 4).forEach(i -> nextLine());
		Integer.parseInt(scanner().skip(".*:").next("\\s*\\d+\\s*")); // projects
		int nJobs = Integer.parseInt(scanner().skip("\n.*:").next("\\s*\\d+\\s*"));
		int horizon = Integer.parseInt(scanner().skip("\n.*:").next("\\s*\\d+\\s*"));
		nextLine();
		nextLine();
		int nRessources = Integer.parseInt(scanner().skip(".*:").next("\\s*\\d+\\s*"));
		nextLine();
		Integer.parseInt(scanner().skip(".*:").next("\\s*\\d+\\s*")); // rn
		nextLine();
		Integer.parseInt(scanner().skip(".*:").next("\\s*\\d+\\s*")); // rd
		IntStream.range(0, 4).forEach(i -> nextLine());
		IntStream.range(0, 6).map(i -> nextInt()).toArray(); // array
		// System.out.println(Kit.join(t));
		IntStream.range(0, 4).forEach(i -> nextLine());
		int[][] successors = IntStream.range(0, nJobs).mapToObj(i -> {
			Kit.control(i + 1 == nextInt(), () -> "i=" + i + " ");
			nextInt(); // mode
			return IntStream.range(0, nextInt()).map(j -> nextInt() - 1).toArray();
		}).toArray(int[][]::new);
		IntStream.range(0, 5).forEach(i -> nextLine());
		int[][] tmp = IntStream.range(0, nJobs).mapToObj(i -> {
			Kit.control(i + 1 == nextInt(), () -> "i=" + i + " ");
			nextInt(); // mode
			return IntStream.range(0, 1 + nRessources).map(j -> nextInt()).toArray();
		}).toArray(int[][]::new);
		int[] durations = Stream.of(tmp).mapToInt(a -> a[0]).toArray();
		int[][] requiredQuantities = Stream.of(tmp).map(a -> Arrays.copyOfRange(a, 1, a.length)).toArray(int[][]::new);
		IntStream.range(0, 4).forEach(i -> nextLine());
		int[] resourceCapacities = IntStream.range(0, nRessources).map(i -> nextInt()).toArray();
		Stream<Object> jobs = IntStream.range(0, nJobs).mapToObj(i -> buildInternClassObject("Job", durations[i], successors[i], requiredQuantities[i]));
		setDataValues(horizon, resourceCapacities, jobs);
	}

}
