package problems.g3_pattern;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

/**
 * Model for the bugs problem. There are bugs of different sorts in a 2 dimensions grid. Each bug of a given type needs a given number of space. The
 * purpose is to delimit rectangles in the grid so that each rectangle: - only contains bugs of the same type. - is the size a bug of this type needs
 * multiplied by the number of bugs in the rectangle.
 */
public class Bugs implements ProblemAPI {
	int height, width;
	Bug[] bugs;
	BugType[] bugTypes;

	class Bug {
		int row, col, type;
	}

	class BugType {
		int length;
		int[] cells;
	}

	boolean neighbors(int i, int j, int k, int l) {
		return i == k && (j == l + 1 || j == l - 1) || j == l && (i == k + 1 || i == k - 1);
	}

	@Override
	public void model() {
		int nBugs = bugs.length, nBugTypes = bugTypes.length;

		Var[][] x = array("x", size(height, width), dom(range(-1, nBugs)), "one variable per square in the grid, whose domain is -1..nbBugs-1");
		Var[] n1 = array("n1", size(nBugs), dom(range(nBugs + 1)), "n1[i] corresponds to the number of squares in x with value i");
		Var[] n2 = array("n2", size(nBugs), dom(range(height * width + 1)),
				"n2[i] corresponds to the number of squares in x with a bug on it and with value i");
		// Var s = var("s", dom(range(nBugs + 1)), "the number of times a bug is in a rectangle whose index is different from the one of the bug");

		forall(range(nBugs), i -> extension(x[bugs[i].row][bugs[i].col], bugTypes[bugs[i].type].cells))
				.note("each bug square can either take its bug index for value or take the one of another bug of the same type");
		forall(range(nBugs), i -> intension(le(x[bugs[i].row][bugs[i].col], i)))
				.note("symmetry breaking: a bug's square's value is smaller or equal to the bug's index");

		// A logical consequence of the previous constraint gives an upper bound for nbSquaresPerIndex variables
		int max = IntStream.range(0, nBugTypes).map(i -> bugTypes[i].cells.length).max().orElse(-1);
		forall(range(nBugTypes).range(1, max), (i, j) -> {
			if (j < bugTypes[i].cells.length)
				intension(le(n1[bugTypes[i].cells[j]], (bugTypes[i].cells.length - j) * bugTypes[i].length));
		});

		// Channeling constraints
		cardinality(vars(x), range(nBugs), occurExactly(n1));
		cardinality(variablesFrom(range(nBugs), i -> x[bugs[i].row][bugs[i].col]), range(nBugs), occurExactly(n2));

		forall(range(nBugs), i -> equal(mul(n2[i], bugTypes[bugs[i].type].length), n1[i]));
		// exactly(n2, 0, s);

		forall(range(height).range(width).range(height).range(width).range(height).range(width), (i, j, k, l, m, n) -> {
			if (i <= k && !neighbors(i, j, k, l) && (i != k || j < l) && i <= m && m <= k && Math.min(j, l) <= n && n <= Math.max(j, l) && (m != i || n != j)
					&& (m != k || n != l))
				intension(or(ne(x[i][j], x[k][l]), eq(x[i][j], x[m][n])));

		}).note("if two squares have the same value, then all the squares in the rectangle they delimit must take this value");

		maximize(SUM, treesFrom(range(nBugs), i -> eq(n2[i], 0)))
				.note("maximizing the number of times a bug is in a rectangle whose index is different from the one of the bug"); // maximize(s)
	}
}

// for (int i = 0; i < height; i++)
// for (int j = 0; j < width; j++)
// for (int k = i; k < height; k++)
// for (int l = 0; l < width; l++)
// if (!neighbors(i, j, k, l) && (i != k || j < l))
// for (int m = i; m <= k; m++)
// for (int n = Math.min(j, l); n <= Math.max(j, l); n++)
// if ((m != i || n != j) && (m != k || n != l))
// intension(or(ne(x[i][j], x[k][l]), eq(x[i][j], x[m][n])));