package problems.g3_pattern;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

/**
 * Model for the Futoshiki problem. The purpose is to put n times each number in 1..n in a n*n grid. Each number must appear exactly once per line and
 * per column. Some hints are given, as well as inequalities over neighboring squares.
 */
public class Futoshiki implements ProblemAPI {
	int size;
	NumberHint[] numHints;
	OperatorHint[] opHints;

	class NumberHint {
		int row, col, number;
	}

	class OperatorHint {
		int row, col;
		boolean lessThan, horizontal;
	}

	@Override
	public void model() {
		Var[][] x = array("x", size(size, size), dom(rangeClosed(1, size)), "x[i][j] is the number put at row i and column j");

		allDifferentMatrix(x);
		forall(range(numHints.length), i -> equal(x[numHints[i].row][numHints[i].col], numHints[i].number)).note("number hints");
		forall(range(opHints.length), i -> {
			Var y = x[opHints[i].row][opHints[i].col];
			Var z = x[opHints[i].row + (opHints[i].horizontal ? 0 : 1)][opHints[i].col + (opHints[i].horizontal ? 1 : 0)];
			if (opHints[i].lessThan)
				lessThan(y, z);
			else
				greaterThan(y, z);
		}).note("operator hints");
	}
}
