package problems.generators;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.Eternity;

public class Eternity_Parser extends Eternity implements ReaderTxt {

	void data() {
		int n = nextInt(), m = nextInt();
		int[][] pieces = range(n * m).range(4).map((i, j) -> nextInt());
		setDataValues(n, m, pieces);
	}
}
