package problems.generators;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.Bugs;

/**
 * Model for the bugs problem. There are bugs of different sorts in a 2 dimensions grid. Each bug of a given type needs a given number of space. The
 * purpose is to delimit rectangles in the grid so that each rectangle: - only contains bugs of the same type. - is the size a bug of this type needs
 * multiplied by the number of bugs in the rectangle.
 */
public class Bugs_Parser extends Bugs implements ReaderTxt {

	void data() {
		nextLine();
		int height = nextInt();
		int width = nextInt();
		nextLine();
		nextLine();
		int nBugTypes = nextInt();
		nextLine();
		nextLine();
		int[] bugTypesLength = valuesFrom(range(nBugTypes), i -> nextInt());
		nextLine();
		nextLine();
		int nBugs = nextInt();
		nextLine();
		nextLine();
		List<Integer>[] lists = range(nBugTypes).mapToObj(i -> new ArrayList<>());
		int[][] t = range(nBugs).mapToObj(i -> vals(nextInt(), nextInt(), nextInt()));
		for (int i = 0; i < t.length; i++)
			lists[t[i][2]].add(i);
		int[][] bugTypesCells = range(nBugTypes).mapToObj(i -> lists[i].stream().mapToInt(v -> v).sorted().toArray());
		Stream<Object> bugs = IntStream.range(0, nBugs).mapToObj(i -> buildInternClassObject("Bug", t[i][0], t[i][1], t[i][2]));
		Stream<Object> bugTypes = IntStream.range(0, nBugTypes).mapToObj(i -> buildInternClassObject("BugType", bugTypesLength[i], bugTypesCells[i]));
		setDataValues(height, width, bugs, bugTypes);
	}
}
// "\nExpected file format for instances : \n\n\n" + "% Size of the grid\n" + "4 6\n" + "% Number of bug types\n" + "2\n"
// + "% Number of required squares for each type of bug\n" + "3 2" + "\n% Number of bugs in the grid\n" + "10\n"
// + "% Bugs positions in the grid (each line for an insect: its two coordinates, and its type)\n" + "0 2 1\n" + "0 3 1\n"