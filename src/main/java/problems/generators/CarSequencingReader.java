package problems.generators;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.CarSequencing;

// time java abscon.Resolution problems.generators.CarSequencingReader ~/instances/vincent/carSequencing/car-dingbas -s=all => 6 sols
public class CarSequencingReader extends CarSequencing implements ReaderTxt {

	void data() {
		nextInt(); // nCars
		int nOptions = nextInt(), nClasses = nextInt();
		int[] blockNum = valuesFrom(range(nOptions), i -> nextInt()), blockDen = valuesFrom(range(nOptions), i -> nextInt());
		int[][] classes = IntStream.range(0, nClasses).mapToObj(i -> IntStream.range(0, nOptions + 1).map(j -> {
			if (j == 0)
				nextInt();
			return nextInt();
		}).toArray()).toArray(int[][]::new);
		int[] demand = columnOf(classes, 0);
		int[][] options = Stream.of(classes).map(t -> Arrays.copyOfRange(t, 1, t.length)).toArray(int[][]::new);
		Stream<Object> carClasses = IntStream.range(0, nClasses).mapToObj(i -> buildInternClassObject("CarClass", demand[i], options[i]));
		Stream<Object> optionLimits = IntStream.range(0, nOptions).mapToObj(i -> buildInternClassObject("OptionLimit", blockNum[i], blockDen[i]));
		setDataValues(carClasses, optionLimits);
	}

	public static void main(String[] args) {
		try (BufferedReader in = new BufferedReader(new InputStreamReader(new FileInputStream("/home/lecoutre/instances/vincent/carSequencing/data.txt")))) {
			for (String line = in.readLine(); line != null; line = in.readLine()) {
				String s = in.readLine().substring("# Problem ".length());
				String name = "car-" + s.substring(0, 2) + "-" + s.substring(3, 5);
				in.readLine();
				PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter("/home/lecoutre/instances/vincent/carSequencing/series1/" + name, true)));
				for (line = in.readLine().trim(); line != null && line.length() != 0; line = in.readLine())
					out.println(line);
				if (line == null)
					break;
				out.close();
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}

// int[] blockNum = range(nOptions).provideVals(i -> readInt()), blockDen = IntStream.range(0, nOptions).map(i -> readInt()).toArray();
