package problems.generators;

import java.util.AbstractMap.SimpleEntry;
import java.util.Scanner;
import java.util.stream.Stream;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.StripPacking;

//found solution with java abscon.Resolution problems.generators.StripPackingReader ~/instances/tdsp/data/series1.txt 0 -ev -rc=10 -st -sing=Last
public class StripPackingReader extends StripPacking implements ReaderTxt {

	void data() {
		Scanner scanner = scanner();
		int number = imp().askInt("number");

		String line = null;
		for (int cnt = 0; cnt <= number; cnt++)
			for (line = nextLine(); line != null && !line.startsWith("name"); line = nextLine())
				;
		String name = line.substring(line.indexOf(":") + 1).trim();
		scanner.findWithinHorizon(":", 0);
		int nRectangles = nextInt();
		scanner.findWithinHorizon(":", 0);
		int containerWidth = nextInt();
		scanner.findWithinHorizon("x", 0);
		int containerHeight = nextInt();
		nextLine();
		line = nextLine();
		// boolean widthFirst = line.startsWith("width");
		Stream<Object> rectangles = Stream.of(range(nRectangles).range(2).map((i, j) -> nextInt())).map(t -> buildInternClassObject("Rectangle", t[0], t[1]));
		imp().parameters.set(0, new SimpleEntry<>(name, null));
		imp().parameters.set(1, new SimpleEntry<>(number, ""));
		Object container = buildInternClassObject("Rectangle", containerWidth, containerHeight);
		setDataValues(container, rectangles);
	}

}
