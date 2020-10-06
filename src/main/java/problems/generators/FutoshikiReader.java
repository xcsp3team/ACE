package problems.generators;

import java.util.ArrayList;
import java.util.List;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.Futoshiki;

public class FutoshikiReader extends Futoshiki implements ReaderTxt {

	void data() {
		nextLine();
		int size = nextInt();
		nextLine();
		nextLine();
		int nHints = nextInt();
		nextLine();
		nextLine();
		List<Object> nlist = new ArrayList<>();
		List<Object> olist = new ArrayList<>();
		for (int i = 0; i < nHints; i++) {
			int row = nextInt(), col = nextInt();
			if (hasNextInt())
				nlist.add(buildInternClassObject("NumberHint", row, col, nextInt()));
			else
				olist.add(buildInternClassObject("OperatorHint", row, col, next().equals("lt"), next().equals("h")));
		}
		setDataValues(size, nlist, olist);

		// System.out.println("Error while looking for the data file.\n\n");
		// System.out.println("\nExpected file format for instances : \n\n\n% Size of the grid\n" + "5\n" + "% Number of hints\n" + "10\n"
		// + "% Hints: coordinates + symbol (number or operator) + v (vertical) or h (horizontal) if operator\n" + "0 0 gt h\n" + "0 2 gt h\n"
		// + "0 3 gt h\n" + "1 0 4\n" + "1 4 2\n" + "2 2 4\n" + "3 3 lt h\n" + "3 4 4\n" + "4 0 lt h\n" + "4 1 lt h\n"
		// + "% Visual representation of the grid (optional, not read by the parser)\n" + "_>_ _>_>_\n" + " \n" + "4 _ _ _ 2\n" + " \n"
		// + "_ _ 4 _ _\n" + " \n" + "_ _ _ _<4\n" + " \n" + "_<_<_ _ _");
	}

}
